(in-package "ACL2")
(program)
(include-book "my-cw")

; (defmacro output-file () "afs/cs.stanford.edu/u/clee0/www/tmp/output.txt")

; TODO better handling of forbidden names... won't actually break right now, but it's pretty inconsistent
(defun forbidden-names ()
  '(nil and or = * + /))

;;; DISPLAY ;;;

; Recursively removes quotes from an expression or list
(mutual-recursion
  (defun remove-quote (expr)
    (if (consp expr)
      (if (fquotep expr)
        (second expr) ; Quoted expression should only have two elements...
        (cons (ffn-symb expr) (remove-quote-lst (fargs expr)))) ; Remove quotes from the arguments to the function
      expr))
  (defun remove-quote-lst (lst)
    (if (endp lst)
      nil
      (cons (remove-quote (car lst)) (remove-quote-lst (cdr lst))))))

; Removes quotes from an association list
(defun remove-quote-alist (alist)
  (if (endp alist)
    nil
    (cons (remove-quote-lst (car alist)) (remove-quote-alist (cdr alist)))))

;;; PROOF PRE-PROCESSING ;;;

; Wrap numbers and constants in quotes
(mutual-recursion
  (defun mark-constants (expr constants)
    (declare (xargs :measure (acl2-count expr)
                    :guard (symbol-listp constants)))
    (cond ((or (acl2-numberp expr) (stringp expr) (member expr constants)) (kwote expr))
          ((fquotep expr) expr)
          ((consp expr) (cons (ffn-symb expr) (mark-constants-lst (fargs expr) constants)))
          (t expr)))
  
  (defun mark-constants-lst (lst constants)
    (declare (xargs :measure (acl2-count lst)
                    :guard (symbol-listp constants)))
    (if (endp lst)
      nil
      (cons (mark-constants (car lst) constants)
            (mark-constants-lst (cdr lst) constants)))))

; Constant-wrapper for rules
(defun mark-constants-rule (rule constants)
  (list (first rule) (mark-constants (second rule) constants) (third rule) (fourth rule)))

; Constant-wrapper for assumptions
(defun mark-constants-assumption (assumption constants)
  (list (first assumption) (mark-constants (second assumption) constants)))

; Constant-wrapper for association list
; Only checks the target; the key in each pair is unaffected
(defun mark-constants-alist (alist constants)
  (if (null alist)
    nil
    (cons (cons (first (first alist))
                (mark-constants-lst (rest (first alist)) constants))
          (mark-constants-alist (rest alist) constants))))

;;; CHECKS FOR WELL-FORMED PROOFS ;;;

; Checks that all elements of a list are atoms
(defun check-atoms-sub (output-file x)
  (if (null x)
    T
    (if (not (atom (first x)))
      (prog2$
        (my-cw output-file "ERROR: ~x0 is not an atom.~%" (remove-quote (first x)))
        nil)
      (check-atoms-sub output-file (rest x)))))

(defun check-atoms (output-file x)
  (if (true-listp x)
    (check-atoms-sub output-file x)
    (prog2$
      (my-cw output-file "ERROR: ~x0 is not a true list.~%" (remove-quote x))
      nil)))

; Check that the mappings in the list are valid:
; 1. Must be a valid association list.
; 2. Must not contain any duplicate names, i.e. keys.
; 3. Keys must all be atoms.
(defun check-mappings (output-file x)
  (if (not (alistp x))
    (prog2$
      (my-cw output-file "ERROR: ~x0 is not a valid association list.~%" (remove-quote x))
      nil)
    (let ((keys (strip-cars x)))
      (cond ((not (no-duplicatesp keys))
             (prog2$
               (my-cw output-file "ERROR: Found duplicate names.~%") ; Any way to tell which name?
               nil))
            ((not (check-atoms output-file keys)) nil)
            (T T)))))

; Returns T if list x contains any numbers, nil otherwise.
(defun contains-numbers (x)
  (if (null x)
    nil
    (if (acl2-numberp (first x))
      T
      (contains-numbers (rest x)))))

; Checks that assumptions are of the correct form (name statement).
; Returns properly formatted assumptions, or nil if there is an error.
; 1. Should be true lists.
; 2. Should have length 2.
; 3. name should be an atom.
; 4. Assumption statement should be a well-formed expression (post-formatting).
(defun prepare-assumptions-sub (output-file x constants)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (my-cw output-file "ERROR: Assumption ~x0 is not in a valid format.~%" (remove-quote (first x)))
           nil))
        ((not (equal (len (first x)) 2))
         (prog2$
           (my-cw output-file "ERROR: Assumption ~x0 does not have length 2.~%" (remove-quote (first x)))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (my-cw output-file "ERROR: ~x0 is not a valid assumption name.~%" (remove-quote (first (first x))))
           nil))
        (T
          (let  ((formatted-assumption (mark-constants-assumption (first x) constants)))
           (if (not (pseudo-termp (second formatted-assumption)))
             (prog2$
               (my-cw output-file "ERROR: Statement ~x0 of assumption ~x1 is not a well-formed expression.~%" (remove-quote (second formatted-assumption)) (remove-quote (first formatted-assumption)))
               nil)
             (let ((formatted-remainder (prepare-assumptions-sub output-file (rest x) constants)))
               (if (and (null formatted-remainder) (rest x))
                 nil ; Failure occurred in a later assumption
                 (cons formatted-assumption formatted-remainder))))))))

; Formats and checks assumptions.
(defun prepare-assumptions (output-file x constants)
  (if (true-listp x)
    (prepare-assumptions-sub output-file x constants)
    (prog2$
      (my-cw output-file "ERROR: Assumptions are not in a valid format: ~x0~%" (remove-quote x))
      nil)))

; Checks that str-vars is in a valid format
(defun check-str-vars (output-file str-vars constants)
  (if (null str-vars)
    T
    (cond ((not (check-atoms output-file str-vars))
           (prog2$
             (my-cw output-file "ERROR: str-vars must be a list of atoms: ~x0.~%" (remove-quote str-vars))
             nil))
          ((not (equal (mark-constants-lst str-vars constants) str-vars))
           (prog2$
             (my-cw output-file "ERROR: str-vars contains constants: ~x0.~%" (remove-quote str-vars))
             nil))
          (T T))))

; Each restriction (element in list) is variable name, followed by a valid restriction (string or number).
; For the future, it can have multiple elements, e.g. ((varname string number)), although this would never be satisfiable.
; TODO Add checks to ensure that a name isn't listed multiple times
(defun check-restrictions-sub (output-file restrictions)
  (if (null restrictions)
    T
    (cond ((not (atom (first (first restrictions))))
           (prog2$
             (my-cw output-file "ERROR: Element ~x0 of restrictions list is not an atom.~%" (remove-quote (first (first restrictions))))
             nil))
          ((set-difference-equal (rest (first restrictions)) '(string number))
           (prog2$
             (my-cw output-file "ERROR: Restriction(s) ~x0 for element ~x1 in restrictions list is not a recognized restriction.~%" (remove-quote (set-difference-equal (rest (first restrictions)) '(string number))) (remove-quote (first (first restrictions))))
             nil))
          (T (check-restrictions-sub output-file (rest restrictions))))))

; Checks that the restrictions given are in a valid format
(defun check-restrictions (output-file restrictions)
  (if (true-list-listp restrictions)
    (check-restrictions-sub output-file restrictions)
    (prog2$
      (my-cw output-file "ERROR: Restrictions list ~x0 is not in a valid format (list of lists).~%" (remove-quote restrictions))
      nil)))

; Checks that rules are of the correct form (name rule-info [str-vars restrictions]).
; str-vars and restrictions are optional.
; Returns properly formatted rules, or nil if there is an error.
; 1. Should be true lists.
; 2. Should have length between 2 and 4
; 3. name should be an atom.
; 4. str-vars, if provided, should be in a valid format.
; 5. restrictions, if provided, should be in a valid format.
; 6. rule-info should be a well-formed expression (post-formatting).
(defun prepare-rules-sub (output-file x constants)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (my-cw output-file "ERROR: Rule ~x0 is not in a valid format.~%" (remove-quote (first x)))
           nil))
        ((or (< (len (first x)) 2) (> (len (first x)) 4))
         (prog2$
           (my-cw output-file "ERROR: Rule ~x0 does not have length between 2 and 4.~%" (remove-quote (first x)))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (my-cw output-file "ERROR: ~x0 is not a valid rule name.~%" (remove-quote (first (first x))))
           nil))
        ((not (check-str-vars output-file (third (first x)) constants))
         nil)
        ((not (check-restrictions output-file (fourth (first x))))
         nil)
        (T
          (let ((formatted-rule (mark-constants-rule (first x) constants)))
           (if (not (pseudo-termp (second formatted-rule)))
             (my-cw output-file "ERROR: Statement ~x0 of rule ~x1 is not a well-formed expression.~%" (remove-quote (second formatted-rule)) (remove-quote (first formatted-rule)))
             (let ((formatted-remainder (prepare-rules-sub output-file (rest x) constants)))
               (if (and (null formatted-remainder) (rest x))
                 nil ; Failure occurred in a later rule
                 (cons formatted-rule formatted-remainder))))))))

; Formats and checks rules.
(defun prepare-rules (output-file x constants)
  (if (true-listp x)
    (prepare-rules-sub output-file x constants)
    (prog2$
      (my-cw output-file "ERROR: Rules are not in a valid format: ~x0~%" (remove-quote x))
      nil)))

; NOTE: If we don't want to allow multiple substitution, this requirement can be enforced for length 2
; Checks that all elements of the association list are pairs.
(defun check-alist-len (output-file x)
  (if (null x)
    T
    (if (equal 2 (len (first x)))
      (check-alist-len output-file (rest x))
      (prog2$
        (my-cw output-file "ERROR: Element ~x0 of association list is not a pair.~%" (remove-quote (first x)))
        nil))))

; Checks that all mappings in the alist are to a list of well-formed expressions.
(defun check-alist-vals (output-file x)
  (cond ((null x) T)
        ((not (pseudo-term-listp (rest (first x))))
         (prog2$
           (my-cw output-file "ERROR: Mapping ~x0 to key ~x1 in association list is not a list of well-formed expressions.~%" (remove-quote (rest (first x))) (remove-quote (first (first x))))
           nil))
        (T (check-alist-vals output-file (rest x)))))

; Checks that association lists have the correct form ((key1 values1) (key2 values2) ...).
; Returns properly formatted association lists, or nil if there is an error.
(defun prepare-alist (output-file x constants)
  (if (not (check-mappings output-file x))
    nil
    (let ((fmt-alist (mark-constants-alist x constants))
          (forbidden-names (append (forbidden-names) constants))
          (keys (strip-cars x)))
      (cond ((intersectp-equal forbidden-names keys)
             (my-cw output-file "ERROR: Found forbidden name(s): ~x0.~%" (remove-quote (intersection-equal forbidden-names keys))))
            ((contains-numbers keys)
             (my-cw output-file "ERROR: Association list may not map to numbers, but it does: ~x0.~%" (remove-quote fmt-alist)))
            ((check-alist-vals output-file fmt-alist) fmt-alist)
            (T nil)))))

(defun check-rulesets (output-file rules rulesets)
  (if (null rulesets)
    (mv T nil)
    (cond ((not (listp (first rulesets)))
           (prog2$
             (my-cw output-file "ERROR: Invalid format for ruleset: ~x0.~%" (first rulesets))
             (mv nil nil)))
          ((< (len (first rulesets)) 2)
           (prog2$
             (my-cw output-file "ERROR: Ruleset is missing ruleset name or rules: ~x0.~%" (first rulesets))
             (mv nil nil)))
          ((not (atom (first (first rulesets))))
           (prog2$
             (my-cw output-file "ERROR: Invalid ruleset name: ~x0.~%" (first (first rulesets)))
             (mv nil nil)))
          (T
            (let ((diff (set-difference-eq (cdr (first rulesets)) (strip-cars rules))))
              (if diff
                (prog2$
                  (my-cw output-file "ERROR: Ruleset ~x0 contains undefined rule(s): ~x1.~%" (first (first rulesets)) diff)
                  (mv nil nil))
                (mv-let (verified rules-in-sets)
                        (check-rulesets output-file rules (rest rulesets))
                        (if verified
                          (mv T (append (cdr (first rulesets)) rules-in-sets))
                          (mv nil nil)))))))))

(defun verify-rulesets (output-file rules rulesets)
  (if (not (listp rulesets))
    (my-cw output-file "ERROR: Invalid format for rulesets list: ~x0.~%" rulesets)
    (mv-let (verified rule-names)
            (check-rulesets output-file rules rulesets)
            (if (not verified)
              nil
              (if (no-duplicatesp rule-names)
                T
                (my-cw output-file "ERROR: Rules cannot be listed in multiple rulesets.~%")))))) ; TODO List which name(s) are duplicated

(defun rule-to-ruleset (rule ruleset)
  (if (null ruleset)
    rule
    (if (member-eq rule (first ruleset))
      (first (first ruleset))
      (rule-to-ruleset rule (rest ruleset)))))

(defun convert-rules (output-file rule-list rules ruleset)
  (if (null rule-list)
    nil
    (if (listp rule-list)
      (if (member-eq (first rule-list) (strip-cars rules))
        (cons (first rule-list) (convert-rules output-file (rest rule-list) rules ruleset))
        (let ((converted (cdr (assoc-eq (first rule-list) ruleset))))
          (if (null converted)
            (my-cw output-file "ERROR: Rule ~x0 is used in proof but undefined.~%" (first rule-list))
            (append (cdr (assoc-eq (first rule-list) ruleset)) (convert-rules output-file (rest rule-list) rules ruleset)))))
      (convert-rules output-file (list rule-list) rules ruleset))))

; Checks that the proof steps are of the correct form (name concl rule-name assoc-list assumptions-used)
; Returns properly formatted proof steps, or nil if there is an error. For each step:
; 1. Should be true lists.
; 2. Should have length 5.
; 3. name should be an atom.
; 4. concl should be a well-formed expression.
; 5. rule-name should be an atom.
; 6. assoc-list should have proper mappings.
; 7. assumptions-used should be a list of atoms.
; 8. Other checks during formatting should all succeed.
(defun prepare-proof-sub (output-file x assumptions rules rulesets constants required)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (my-cw output-file "ERROR: Proof step ~x0 is not in a valid format.~%" (remove-quote (first x)))
           nil))
        ((not (equal (len (first x)) 5))
         (prog2$
           (my-cw output-file "ERROR: Proof step ~x0 does not have length 5.~%" (remove-quote (first x)))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (my-cw output-file "ERROR: ~x0 is not a valid proof step name.~%" (remove-quote (first (first x))))
           nil))
        (T
          (let ((fmt-concl (mark-constants (second (first x)) constants)))
            (cond ((not (pseudo-termp fmt-concl))
                   (prog2$
                     (my-cw output-file "ERROR: Conclusion ~x0 of proof step ~x1 is not a well-formed expression.~%" (remove-quote fmt-concl) (remove-quote (first (first x))))
                     nil))
                  ((not (alistp (fourth (first x))))
                   (prog2$
                     (my-cw output-file "ERROR: ~x0 is not a valid association list in proof step ~x1.~%" (remove-quote (fourth (first x))) (remove-quote (first (first x))))
                     nil))
                  ((not (check-atoms output-file (fifth (first x))))
                   (my-cw output-file "ERROR: ~x0 is not a valid list of assumptions in proof step ~x1.~%" (fifth (first x)) (first (first x))))
                  ((set-difference-eq (fifth (first x)) (strip-cars assumptions))
                   (my-cw output-file "ERROR: Step ~x0 uses undefined assumption(s) ~x1.~%" (first (first x)) (set-difference-eq (fifth (first x)) (strip-cars assumptions))))
                  (T
                    (let ((fmt-alist (prepare-alist output-file (fourth (first x)) constants)))
                      (if (and (null fmt-alist) (fourth (first x)))
                        nil ; There was a problem with the association list.
                        (if (and (member 'r required) (listp (third (first x))) (not (equal 1 (len (third (first x))))))
                          (my-cw output-file "ERROR: Step ~x0 must list exactly one rule or ruleset.~%" (first (first x)) (third (first x)))
                          (let ((fmt-rules (convert-rules output-file (third (first x)) rules rulesets)))
                            (if (and (null fmt-rules) (third (first x)))
                              nil
                              (let ((formatted-pfstep (list (first (first x)) fmt-concl fmt-rules fmt-alist (fifth (first x))))
                                    (formatted-remainder (prepare-proof-sub output-file (rest x) (append assumptions (list (first x))) rules rulesets constants required)))
                                (if (and (null formatted-remainder) (rest x))
                                  nil ; Failure occurred in a later rule
                                  (cons formatted-pfstep formatted-remainder))))))))))))))

; Formats and checks the proof.
(defun prepare-proof (output-file x assumptions rules rulesets constants required)
  (if (true-listp x)
    (prepare-proof-sub output-file x assumptions rules rulesets constants required)
    (prog2$
      (my-cw output-file "ERROR: Proof is not in a valid format: ~x0~%" (remove-quote x))
      nil)))

; Formats and checks the requirements list.
(defun prepare-required (output-file required)
  (if (true-listp required)
    (let* ((allowed (list 'r 'a 's))
           (diff (set-difference-eq required allowed)))
      (if diff
        (my-cw output-file "ERROR: Required elements contains invalid arguments: ~x0~%" diff)
        (let ((fmt-required (remove-duplicates required)))
          (if (not (member 'r fmt-required))
            (if (member 'a fmt-required)
              (prog2$
                (my-cw output-file "WARNING: Required elements contain a but not r. Adding r to required elements.~%")
                (cons 'r fmt-required))
              (if (member 's fmt-required)
                (prog2$
                  (my-cw output-file "WARNING: Required elements contain s but not r. Adding r to required elements.~%")
                  (cons 'r fmt-required))
                fmt-required))
            fmt-required))))
    (my-cw output-file "ERROR: Required elements are not in a valid format: ~x0~%" required)))
