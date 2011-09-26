(in-package "ACL2")
(program)

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
(defun check-atoms-sub (x)
  (if (null x)
    T
    (if (not (atom (first x)))
      (prog2$
        (cw "ERROR: ~x0 is not an atom.~%" (first x))
        nil)
      (check-atoms-sub (rest x)))))

(defun check-atoms (x)
  (if (true-listp x)
    (check-atoms-sub x)
    (prog2$
      (cw "ERROR: ~x0 is not a true list.~%" x)
      nil)))

; Check that the mappings in the list are valid:
; 1. Must be a valid association list.
; 2. Must not contain any duplicate names, i.e. keys.
; 3. Keys must all be atoms.
(defun check-mappings (x)
  (if (not (alistp x))
    (prog2$
      (cw "ERROR: ~x0 is not a valid association list.~%" x)
      nil)
    (let ((keys (strip-cars x)))
      (cond ((not (no-duplicatesp keys))
             (prog2$
               (cw "ERROR: Found duplicate names.~%") ; Any way to tell which name?
               nil))
            ((not (check-atoms keys)) nil)
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
(defun prepare-assumptions-sub (x constants)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (cw "ERROR: Assumption ~x0 is not in a valid format.~%" (first x))
           nil))
        ((not (equal (len (first x)) 2))
         (prog2$
           (cw "ERROR: Assumption ~x0 does not have length 2.~%" (first x))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (cw "ERROR: ~x0 is not a valid assumption name.~%" (first (first x)))
           nil))
        (T
          (let  ((formatted-assumption (mark-constants-assumption (first x) constants)))
           (if (not (pseudo-termp formatted-assumption))
             (prog2$
               (cw "ERROR: Statement ~x0 of assumption ~x1 is not a well-formed expression.~%" (second formatted-assumption) (first formatted-assumption))
               nil)
             (let ((formatted-remainder (prepare-assumptions-sub (rest x) constants)))
               (if (and (null formatted-remainder) (rest x))
                 nil ; Failure occurred in a later assumption
                 (cons formatted-assumption formatted-remainder))))))))

(defun prepare-assumptions (x constants)
  (if (true-listp x)
    (prepare-assumptions-sub x constants)
    (prog2$
      (cw "ERROR: Assumptions are not in a valid format: ~x0~%" x)
      nil)))

(defun check-str-vars (str-vars constants)
  (if (null str-vars)
    T
    (cond ((not (check-atoms str-vars))
           (prog2$
             (cw "ERROR: str-vars must be a list of atoms: ~x0.~%" str-vars)
             nil))
          ((not (equal (mark-constants-lst str-vars constants) str-vars))
           (prog2$
             (cw "ERROR: str-vars contains constants: ~x0.~%" str-vars)
             nil))
          (T T))))

; For now, restrictions can only have one per variable
(defun check-restrictions-sub (restrictions)
  (if (null restrictions)
    T
    (cond ((not (atom (first (first restrictions))))
           (prog2$
             (cw "ERROR: Element ~x0 of restrictions list is not an atom.~%" (first (first restrictions)))
             nil))
          ((set-difference-equal (rest (first restrictions)) '(string number))
           (prog2$
             (cw "ERROR: Restriction(s) ~x0 for element ~x1 in restrictions list is not a recognized restriction.~%" (set-difference-equal (rest (first restrictions)) '(string number)) (first (first restrictions)))
             nil))
          (T (check-restrictions-sub (rest restrictions))))))

(defun check-restrictions (restrictions)
  (if (true-list-listp restrictions)
    (check-restrictions-sub restrictions)
    (prog2$
      (cw "ERROR: Restrictions list ~x0 is not in a valid format (list of lists).~%" restrictions)
      nil)))

; Checks that rules are of the correct form (name rule-info)
; Returns properly formatted rules, or nil if there is an error.
; 1. Should be true lists.
; 2. Should have length 2 or 3.
; 3. name should be an atom.
; 4. rule-info should be a well-formed expression (post-formatting).
(defun prepare-rules-sub (x constants)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (cw "ERROR: Rule ~x0 is not in a valid format.~%" (first x))
           nil))
        ((not (or (> (len (first x)) 2) (< (len (first x)) 4)))
         (prog2$
           (cw "ERROR: Rule ~x0 does not have length between 2 and 4.~%" (first x))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (cw "ERROR: ~x0 is not a valid rule name.~%" (first (first x)))
           nil))
        ((not (check-str-vars (third (first x)) constants))
         nil)
        ((not (check-restrictions (fourth (first x))))
         nil)
        (T
          (let ((formatted-rule (mark-constants-rule (first x) constants)))
           (if (not (pseudo-termp (second formatted-rule)))
             (prog2$
               (cw "ERROR: Statement ~x0 of rule ~x1 is not a well-formed expression.~%" (second formatted-rule) (first formatted-rule))
               nil)
             (let ((formatted-remainder (prepare-rules-sub (rest x) constants)))
               (if (and (null formatted-remainder) (rest x))
                 nil ; Failure occurred in a later rule
                 (cons formatted-rule formatted-remainder))))))))

(defun prepare-rules (x constants)
  (if (true-listp x)
    (prepare-rules-sub x constants)
    (prog2$
      (cw "ERROR: Rules are not in a valid format: ~x0~%" x)
      nil)))

; NOTE: If we don't want to allow multiple substitution, this requirement can be enforced for length 2
; Checks that all elements of the association list are pairs
(defun check-alist-len (x)
  (if (null x)
    T
    (if (equal 2 (len (first x)))
      (check-alist-len (rest x))
      (prog2$
        (cw "ERROR: Element ~x0 of association list is not a pair.~%" (first x))
        nil))))

; Checks that all mappings in the alist are to a list of well-formed expressions.
(defun check-alist-vals (x)
  (cond ((null x) T)
        ((not (pseudo-term-listp (rest (first x))))
         (prog2$
           (cw "ERROR: Mapping ~x0 to key ~x1 in association list is not a list of well-formed expressions.~%" (rest (first x)) (first (first x)))
           nil))
        (T (check-alist-vals (rest x)))))

; Checks that association lists have the correct form ((key1 values1) (key2 values2) ...).
; Returns properly formatted association lists, or nil if there is an error.
(defun prepare-alist (x constants)
  (if (not (check-mappings x))
    nil
    (let ((fmt-alist (mark-constants-alist x constants))
          (forbidden-names (append '(nil and or = * + /) constants))
          (keys (strip-cars x)))
      (cond ((intersectp-equal forbidden-names keys)
             (prog2$
               (cw "ERROR: Found forbidden name(s): ~x0.~%" (intersection-equal forbidden-names keys))
               nil))
            ((contains-numbers keys)
             (prog2$
               (cw "ERROR: Association list may not map to numbers, but it does: ~x0.~%" fmt-alist)
               nil))
            ((check-alist-vals fmt-alist) fmt-alist)
            (T nil)))))

; Checks that the proof steps are of the correct form (name concl rule-name assoc-list)
; Returns properly formatted proof steps, or nil if there is an error.
; 1. Should be true lists.
; 2. Should have length 4.
; 3. name should be an atom.
; 4. concl should be a well-formed expression.
; 5. rule-name should be an atom.
; 6. assoc-list should have proper mappings.
(defun prepare-proof-sub (x constants)
  (cond ((null x) nil)
        ((not (true-listp (first x)))
         (prog2$
           (cw "ERROR: Proof step ~x0 is not in a valid format.~%" (first x))
           nil))
        ((not (equal (len (first x)) 4))
         (prog2$
           (cw "ERROR: Proof step ~x0 does not have length 4.~%" (first x))
           nil))
        ((not (atom (first (first x))))
         (prog2$
           (cw "ERROR: ~x0 is not a valid proof step name.~%" (first (first x)))
           nil))
        (T
          (let ((fmt-concl (mark-constants (second (first x)) constants)))
            (cond ((not (pseudo-termp fmt-concl))
                   (prog2$
                     (cw "ERROR: Conclusion ~x0 of proof step ~x1 is not a well-formed expression.~%" fmt-concl (first (first x)))
                     nil))
                  ((not (atom (third (first x))))
                   (prog2$
                     (cw "ERROR: ~x0 is not a valid rule name in proof step ~x1.~%" (third (first x)) (first (first x)))
                     nil))
                  ((not (alistp (fourth (first x))))
                   (prog2$
                     (cw "ERROR: ~x0 is not a valid association list in proof step ~x1.~%" (fourth (first x)) (first (first x)))
                     nil))
                  (T
                    (let ((fmt-alist (prepare-alist (fourth (first x)) constants)))
                      (if (and (null fmt-alist) (fourth (first x)))
                        nil ; There was a problem with the association list.
                        (let ((formatted-pfstep (list (first (first x)) fmt-concl (third (first x)) fmt-alist))
                              (formatted-remainder (prepare-proof-sub (rest x) constants)))
                          (if (and (null formatted-remainder) (rest x))
                            nil ; Failure occurred in a later rule
                            (cons formatted-pfstep formatted-remainder)))))))))))

(defun prepare-proof (x constants)
  (if (true-listp x)
    (prepare-proof-sub x constants)
    (prog2$
      (cw "ERROR: Proof is not in a valid format: ~x0~%" x)
      nil)))
