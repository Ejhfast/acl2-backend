(in-package "ACL2")
(program)
(include-book "proof-formatter")
(include-book "my-cw")

;;;;;;;;;;;;;;;;;;;;;;;;
;;; HELPER FUNCTIONS ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

; Returns list of elements associated with list of keys
(defun get-rules (rule-list rules)
  (if (null rule-list)
    nil
    (cons (assoc-equal (first rule-list) rules) (get-rules (rest rule-list) rules))))

; Returns true if the list is a list of assumptions
(defun list-of-assumptions (lst)
  (if (null lst)
    T
    (if (= (len (first lst)) 2)
      (list-of-assumptions (rest lst))
      nil)))

; Returns the values corresponding to a given key
(defun get-value (key pairs)
  (let ((result (assoc-equal key pairs)))
    (if (null result)
      nil
      (rest result))))

; Get requirements and conclusions for rule
; Returns (mv rule-concl rule-reqs str-vars restrictions)
; Removes the "and" from rule-reqs, if it exists
(defun get-rule-info (rule)
  (let ((rule-stmt (second rule))
        (str-vars (third rule))
        (restrictions (fourth rule)))
    (cond ((not (equal (car rule-stmt) 'implies))
           (mv rule-stmt nil str-vars restrictions)) ; No requirements
          ((equal (caadr rule-stmt) 'and)
           (mv (caddr rule-stmt) (cdadr rule-stmt) str-vars restrictions)) ; More than one requirement, strip and
          (T
            (mv (third rule-stmt) (list (second rule-stmt)) str-vars restrictions))))) ; One requirement

; Returns (mv first second), where first has length nummatch and second has the rest
(defun list-split (nummatch terms)
  (if (equal nummatch 0)
    (mv nil terms)
    (mv-let (head tail)
            (list-split (- nummatch 1) (cdr terms))
            (mv (cons (car terms) head) tail))))

; Checks if wrapped is a quoted number
(defun check-number (wrapped)
  (if (equal (len wrapped) 1)
    (let ((x (first wrapped)))
      (and (not (atom x)) (equal (len x) 2) (equal (first x) 'quote) (acl2-numberp (second x))))
    nil))

; Checks if wrapped is a quoted string
(defun check-string (wrapped)
  (if (equal (len wrapped) 1)
    (let ((x (first wrapped)))
      (and (not (atom x)) (equal (len x) 2) (equal (first x) 'quote) (stringp (second x))))
    nil))

; Check that the given substitutions obey the restrictions and do not substitute for a literal
(defun check-subs (subs str-vars restrictions)
  (if (null subs)
    T
    (let ((var (first (first subs)))
          (sub (rest (first subs))))
      (cond ((and (not (member var str-vars)) (not (equal (len sub) 1)))
             nil)
            ((and (member 'number (get-value var restrictions)) (not (check-number sub)))
             nil)
            ((and (member 'string (get-value var restrictions)) (not (check-string sub)))
             nil)
            (T (check-subs (rest subs) str-vars restrictions))))))

; Helper function for parsing function call
(defmacro call-of (fn term)
  `(and (consp ,term)
        (eq ,fn (ffn-symb ,term))))
(defmacro empty-alist () nil)

(mutual-recursion
  ; Using the associations in alist, makes the appropriate substitutions in every element in expression lst.
  (defun my-sublis-var-lst (lst alist)
    (declare (xargs :measure (acl2-count lst)
                    :guard (and (symbol-alistp alist)
                                (pseudo-term-listp lst))))
    (if (endp lst)
      nil
      (let ((subbed (my-sublis-var (car lst) alist)))
        (append subbed (my-sublis-var-lst (cdr lst) alist)))))

  (defun my-sublis-var (form alist)
    (declare (xargs :measure (acl2-count form)
                    :guard (and (symbol-alistp alist)
                                (pseudo-termp form))))
    (cond ((variablep form)
           (let ((a (assoc-eq form alist)))
             (cond (a (cdr a))
                   (t (list form)))))
          ((fquotep form) (list form))
          (t (list (cons (ffn-symb form) (my-sublis-var-lst (fargs form) alist)))))))

; Also inserts toprove clauses
(defun sub-all-terms (subst-into subs)
  (if (null subst-into)
    nil
    (cons (cons 'toprove (my-sublis-var (first subst-into) subs)) (sub-all-terms (rest subst-into) subs))))

(defun sub-all (subst-into subs-list)
  (if (null subs-list)
    nil
    (cons (sub-all-terms subst-into (first subs-list)) (sub-all subst-into (rest subs-list)))))

; Pull a list of all free variables from a term
(defmacro empty-acc () nil)
(mutual-recursion
  (defun get-vars-from-term-aux (term acc)
    (if (atom term)
      (add-to-set-eq term acc)
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
          acc
          (get-vars-from-term-aux-lst (fargs term) acc)))))

  (defun get-vars-from-term-aux-lst (terms acc)
    (if (endp terms)
      acc
      (get-vars-from-term-aux-lst (rest terms)
                                  (get-vars-from-term-aux (first terms) acc)))))

(defun get-vars-from-term (term)
  (get-vars-from-term-aux term (empty-acc)))

(defun get-vars-from-term-lst (term-lst)
  (if (null term-lst)
    nil
    (append (get-vars-from-term (first term-lst)) (get-vars-from-term-lst (rest term-lst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FOR DISPLAYING PROOF-RESULTS ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-stmts (proof-path)
  (if (null proof-path)
    nil
    (cons (remove-quote (second (first proof-path))) (extract-stmts (rest proof-path)))))

(mutual-recursion
  (defun display-proof-step (output-file proof-path rulesets)
    (if (= (len proof-path) 2)
      nil ; Of the form (T ASSUMPTION), for which no printing needs to be done
      (let ((stmt (second proof-path))
            (rule-used (third proof-path))
            (assumptions (cdddr proof-path)))
        (prog2$
          (display-proof-step-list output-file assumptions rulesets)
          (let ((ruleset-name (rule-to-ruleset rule-used rulesets)))
            (if (equal ruleset-name rule-used)
              (my-cw output-file "Successfully proved ~x0 using rule ~x1 and assumptions ~x2.~%" (remove-quote stmt) rule-used (extract-stmts assumptions))
              (my-cw output-file "Successfully proved ~x0 using ruleset ~x1 and assumptions ~x2.~%" (remove-quote stmt) ruleset-name (extract-stmts assumptions))))))))
  
  (defun display-proof-step-list (output-file proof-path-list rulesets)
    (if (null proof-path-list)
      nil
      (prog2$
        (if (not (atom (first proof-path-list)))
          (display-proof-step output-file (first proof-path-list) rulesets)
          nil)
        (display-proof-step-list output-file (rest proof-path-list) rulesets)))))

(defun report-success-base (output-file step-name proof-path rulesets)
  (prog2$
    (prog2$
      (if (list-of-assumptions (cdddr proof-path))
        (my-cw output-file "Step ~x0: " step-name)
        (my-cw output-file "Step ~x0: Proved in multiple steps:~%" step-name))
      (display-proof-step output-file proof-path rulesets))
    T))

;;;;;;;;;;;;;;;;;;;;;;;
;;; PROOF FUNCTIONS ;;;
;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
  (defun unify-stmts (output-file pattern term rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
    (if (atom pattern) ; Mapping here is unambiguous
      (if (member pattern (strip-cars subs)) ; If there is already a mapping
        (let ((match (get-value pattern subs)))
          (if (equal term match) ; Does it match previous mapping?
            (continue-unifications-concl output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
            (mv nil nil nil))) ; Does not match previous mapping
        (if (null pattern)
          (if (equal '(nil) term)
            (continue-unifications-concl output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used) ; Both are nil
            (mv nil nil nil)) ; Cannot map something to nil
          (if (member 's required)
            (prog2$
              (my-cw output-file "Substitutions are required; missing substitution for ~x0, aborting.~%" (remove-quote pattern))
              (mv nil nil nil))
            (let ((newsub (list (cons pattern term)))) ; We may have just found a new substitution to use
              (if (check-subs newsub str-vars restrictions)
                (continue-unifications-concl output-file rest-unifications str-vars restrictions (append subs newsub) rule-reqs assumptions required assumptions-used)
                (mv nil nil nil))))))
      (if (equal (len term) 1) ; If pattern is a list, term should be a list in a list
        (let ((term-list (first term))
              (pat-fn (ffn-symb pattern)))
          (if (eq 'quote pat-fn)
            (if (equal term-list pattern) ; Quoted terms must match
              (continue-unifications-concl output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
              (mv nil nil nil))
            (if (call-of pat-fn term-list) ; Two function calls must have matching functions
              (match-lists-stmts output-file (fargs pattern) (fargs term-list) rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
              (mv nil nil nil))))
        (mv nil nil nil))))

  (defun match-lists-stmts (output-file patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
    (if (endp patterns)
      (if (endp terms) ; nil must match nil
        (continue-unifications-concl output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
        (mv nil nil nil))
      (let ((match (assoc-eq (car patterns) subs))) ; True if there is a preexisting substitution for the next term to process
        (if match
          (if (>= (len terms) (len (cdr match)))
            ; Preexisting substitution fixes the number of terms that can be unified in the next step
            (unify-stmts-lst output-file (len (cdr match)) (len (cdr match)) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
            (mv nil nil nil))
          (if (member-eq (car patterns) str-vars)
            ; Next element in patterns is allowed to map to a string
            (unify-stmts-lst output-file 0 (len terms) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
            (if (equal (len terms) 0)
              ; Need to match to one term, but there are none left
              (mv nil nil nil)
              ; Next element in patterns must match to exactly one term
              (unify-stmts-lst output-file 1 1 patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)))))))

  (defun unify-stmts-lst (output-file num-to-match max-to-match patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
    (mv-let (head-terms tail-terms)
            (list-split num-to-match terms)
            ; Unify with the appropriate subset of terms
            (mv-let (success new-subs-used new-assumptions-used)
                    (unify-stmts output-file (first patterns) head-terms (cons (list (rest patterns) tail-terms) rest-unifications) str-vars restrictions subs rule-reqs assumptions required assumptions-used)
                    (if success
                      (mv T new-subs-used new-assumptions-used)
                      (if (< num-to-match max-to-match)
                        (unify-stmts-lst output-file (+ num-to-match 1) max-to-match patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
                        (mv nil nil nil))))))

  (defun continue-unifications-concl (output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required assumptions-used)
    (if (null rest-unifications)
      (if (null rule-reqs)
        (mv T subs assumptions-used)
        (if (member 'a required)
          (unify-stmts output-file (first rule-reqs) (cdr (first assumptions)) rest-unifications str-vars restrictions subs (rest rule-reqs) (rest assumptions) required (append assumptions-used (list (list T (first (first assumptions))))))
          (find-assumptions-in-pool output-file rule-reqs assumptions assumptions str-vars restrictions subs required assumptions-used)))
      (match-lists-stmts output-file (first (first rest-unifications)) (second (first rest-unifications)) (rest rest-unifications) str-vars restrictions subs rule-reqs assumptions required assumptions-used)))

  ; rule-reqs should not be null
  (defun find-assumptions-in-pool (output-file rule-reqs assumptions-left assumptions str-vars restrictions subs required assumptions-used)
    (if (null assumptions-left)
      (mv nil nil nil) ; No assumptions left to try
      (mv-let (success new-subs new-assumptions-used)
              (unify-stmts output-file (first rule-reqs) (cdr (first assumptions-left)) nil str-vars restrictions subs (rest rule-reqs) assumptions required (append assumptions-used (list (list T (first (first assumptions-left))))))
              (if success
                (mv T new-subs new-assumptions-used)
                (find-assumptions-in-pool output-file rule-reqs (rest assumptions-left) assumptions str-vars restrictions subs required assumptions-used))))))

(defun check-concl (output-file rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions required)
  (if (check-subs given-subs str-vars restrictions)
    (unify-stmts output-file rule-concl (list step-concl) nil str-vars restrictions given-subs rule-reqs assumptions required nil)
    (mv nil nil nil)))

; Returns (mv nil nil) if proof fails, others (mv T (T STMT RULE ASSUMP1 ASSUMP2 ...))
(defun prove-in-one-step (output-file assumptions rules step-concl given-subs required)
  (if (null rules)
    (mv nil nil) ; No rules left - fails
    (let* ((rule-used (first rules)))
      (mv-let (rule-concl rule-reqs str-vars restrictions)
              (get-rule-info rule-used)
              (if (and (member 'a required) (not (equal (len assumptions) (len rule-reqs))))
                (prove-in-one-step output-file assumptions (rest rules) step-concl given-subs required)
                (mv-let (success subs assumptions-used)
                        (check-concl output-file rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions required)
                        (declare (ignore subs)) ; TODO include these later!
                        (if success
                          (mv T (cons T (cons step-concl (cons (first rule-used) assumptions-used))))
                          (prove-in-one-step output-file assumptions (rest rules) step-concl given-subs required))))))))

; TODO Should rename... is really "has free variables in rule requirements not named in conclusion"
(defun has-free-vars (rule)
  (mv-let (rule-concl rule-reqs str-vars restrictions)
          (get-rule-info rule)
          (declare (ignore str-vars restrictions))
          (let ((terms-in-concl (get-vars-from-term rule-concl))
                (terms-in-reqs (get-vars-from-term-lst rule-reqs)))
            (set-difference-equal terms-in-reqs terms-in-concl))))

(mutual-recursion
  (defun generate-all-subs (pattern term rest-unifications str-vars restrictions subs subs-list)
    (if (atom pattern) ; Mapping here is unambiguous
      (if (member pattern (strip-cars subs)) ; If there is already a mapping
        (let ((match (get-value pattern subs)))
          (if (equal term match) ; Does it match previous mapping?
            (continue-unifications rest-unifications str-vars restrictions subs subs-list)
            subs-list))
        (if (null pattern)
          (if (equal '(nil) term)
            (continue-unifications rest-unifications str-vars restrictions subs subs-list)
            subs-list) ; Cannot map something to nil
          (let ((newsub (list (cons pattern term)))) ; We may have just found a new substitution to use
            (if (check-subs newsub str-vars restrictions)
              (continue-unifications rest-unifications str-vars restrictions (append subs newsub) subs-list)
              subs-list))))
      (if (equal (len term) 1) ; If pattern is a list, term should be a list in a list
        (let ((term-list (first term))
              (pat-fn (ffn-symb pattern)))
          (if (eq 'quote pat-fn)
            (if (equal term-list pattern) ; Quoted terms must match
              (continue-unifications rest-unifications str-vars restrictions subs subs-list)
              subs-list)
            (if (call-of pat-fn term-list) ; Two function calls must match
              (match-lists (fargs pattern) (fargs term-list) rest-unifications str-vars restrictions subs subs-list)
              subs-list)))
        subs-list)))

  (defun match-lists (patterns terms rest-unifications str-vars restrictions subs subs-list)
    (if (endp patterns)
      (if (endp terms) ; nil must match nil
        (continue-unifications rest-unifications str-vars restrictions subs subs-list)
        subs-list)
      (let ((match (assoc-eq (car patterns) subs))) ; True if there is a preexisting substitution for the next term to process
        (if match
          (if (>= (len terms) (len (cdr match))) ; Is there a chance this is consistent with the preexisting substitution for the next term?
            (generate-all-subs-lst (len (cdr match)) (len (cdr match)) patterns terms rest-unifications str-vars restrictions subs subs-list)
            subs-list)
          (if (member-eq (car patterns) str-vars) ; Can the next term match multiple terms?
            (generate-all-subs-lst 0 (len terms) patterns terms rest-unifications str-vars restrictions subs subs-list)
            (if (equal (len terms) 0)
              subs-list ; Must match exactly one term, but there are none left
              (generate-all-subs-lst 1 1 patterns terms rest-unifications str-vars restrictions subs subs-list)))))))

  (defun generate-all-subs-lst (num-to-match max-to-match patterns terms rest-unifications str-vars restrictions subs subs-list)
    (mv-let (head-terms tail-terms)
            (list-split num-to-match terms)
            ; Unify with the appropriate subset of terms
            (let ((subs-list (generate-all-subs (first patterns) head-terms (cons (list (rest patterns) tail-terms) rest-unifications) str-vars restrictions subs subs-list)))
              (if (< num-to-match max-to-match)
                ; If unification failed and you are allowed to match with more terms, try unification with a longer term list
                (generate-all-subs-lst (+ num-to-match 1) max-to-match patterns terms rest-unifications str-vars restrictions subs subs-list)
                subs-list))))

  (defun continue-unifications (rest-unifications str-vars restrictions subs subs-list)
    (if (null rest-unifications)
      (cons subs subs-list)
      (match-lists (first (first rest-unifications)) (second (first rest-unifications)) (rest rest-unifications) str-vars restrictions subs subs-list))))

(defun insert-useforproofs (rule-name list-stmts)
  (if (null list-stmts)
    nil
    (cons (cons 'useforproof (cons rule-name (first list-stmts))) (insert-useforproofs rule-name (rest list-stmts)))))

(defun get-needed-assumptions-list (to-expand rule)
  (mv-let (rule-concl rule-reqs str-vars restrictions)
          (get-rule-info rule)
          (let ((subs-list (generate-all-subs rule-concl (list to-expand) nil str-vars restrictions nil nil)))
            (insert-useforproofs (first rule) (sub-all rule-reqs subs-list)))))

(defun expand-proof-paths (to-expand rules)
  (if (null rules)
    nil
    (let ((rest-expansions (expand-proof-paths to-expand (cdr rules))))
      (if (has-free-vars (first rules))
        rest-expansions
        (let ((first-expansions (get-needed-assumptions-list to-expand (first rules))))
          (append first-expansions rest-expansions))))))

(defun expand-no-free-vars (to-expand rules)
  (if (null rules)
    nil
    (let ((proof-paths (expand-proof-paths to-expand rules)))
      (if (null proof-paths)
        nil
        (cons 'canprove (cons to-expand (expand-proof-paths to-expand rules)))))))

; Attempt to prove the given conclusion with the available rules and assumptions
(defun prove-stmt (output-file assumptions rules step-concl given-subs required depth)
  ; Ensure that we haven't already proved the conclusion
  (let ((matching-assumption (rassoc-equal (list step-concl) assumptions)))
    (if (null matching-assumption)
      ; First, attempt to prove in one step
      (mv-let (success proof-details)
              (prove-in-one-step output-file assumptions rules step-concl given-subs required)
              (if success
                (mv success proof-details)
                (if (< depth 1)
                  (mv nil nil) ; Not permitted to skip steps
                  (mv nil (expand-no-free-vars step-concl rules))))) ; If we have recursion depth left, return a tree of possible proof methods
      (mv T (cons T (cons (first matching-assumption) nil))))))

(mutual-recursion
  (defun prove-tree (output-file assumptions rules to-prove depth)
    (let ((prefix (ffn-symb to-prove)))
      (cond ((equal 'canprove prefix)
             (if (>= (len to-prove) 3)
               (let ((stmt (second to-prove))
                     (expanded-list (prove-tree-canprove output-file assumptions rules (cddr to-prove) depth)))
                 (if (null expanded-list)
                   nil
                   (cons 'canprove (cons stmt expanded-list))))
               (my-cw output-file "ERROR: Invalid canprove term detected: ~x0.~%" to-prove)))
            ((equal 'useforproof prefix)
             (if (>= (len to-prove) 3)
               (let ((rule-used (second to-prove))
                     (expanded-list (prove-tree-useforproof output-file assumptions rules (cddr to-prove) depth)))
                 (if (null expanded-list)
                   nil
                   (cons 'useforproof (cons rule-used expanded-list))))
               (my-cw output-file "ERROR: Invalid useforproof term detected: ~x0.~%" to-prove)))
            ((equal T prefix) to-prove) ; Completed proof on this branch, no further work needed
            ((equal 'toprove prefix)
             (if (equal (len to-prove) 2)
               (mv-let (success proof-details)
                       (prove-stmt output-file assumptions rules (second to-prove) nil nil depth)
                       (declare (ignore success))
                       proof-details)
               (my-cw output-file "ERROR: Invalid toprove clause detected: ~x0.~%" to-prove)))
            (T (my-cw output-file "ERROR: Unrecognized branch ~x0~%" to-prove)))))

  (defun prove-tree-canprove (output-file assumptions rules to-prove-list depth)
    (if (null to-prove-list)
      nil
      (let* ((first-to-prove (first to-prove-list))
             (processed-first (prove-tree output-file assumptions rules first-to-prove depth))
             (processed-rest (prove-tree-canprove output-file assumptions rules (cdr to-prove-list) depth)))
        (if (null processed-first)
          processed-rest
          (cons processed-first processed-rest)))))
  
  (defun prove-tree-useforproof (output-file assumptions rules to-prove-list depth)
    (let* ((first-to-prove (first to-prove-list))
           (processed-first (prove-tree output-file assumptions rules first-to-prove depth)))
      (if (null processed-first)
        nil
        (if (equal (len to-prove-list) 1)
          (list processed-first)
          (let ((processed-rest (prove-tree-useforproof output-file assumptions rules (cdr to-prove-list) depth)))
            (if (null processed-rest)
              nil
              (cons processed-first processed-rest))))))))

; Returns (mv nil nil) if it does not, (mv T proof-path) if it does
(mutual-recursion
  (defun contains-proof (tree)
    (if (null tree)
      (mv nil nil)
      (if (atom tree)
        (mv T tree) ; Only an atom, so it must be a known assumption
        (let ((prefix (ffn-symb tree)))
          (cond ((equal 'canprove prefix)
                 (contains-proof-canprove tree))
                ((equal 'useforproof prefix)
                 (contains-proof-useforproof tree))
                ((equal 'T prefix)
                 (mv T tree))
                (T (mv nil nil)))))))

  (defun contains-proof-canprove (canprove-clause)
    (let ((stmt (second canprove-clause))
          (possible-proofs (cddr canprove-clause)))
      (mv-let (success reduction)
              (contains-proof-or possible-proofs)
              (if success
                (mv T (cons T (cons stmt reduction)))
                (mv nil nil)))))

  (defun contains-proof-or (stmt-list)
    (if (null stmt-list)
      (mv nil nil)
      (mv-let (success reduction)
              (contains-proof (first stmt-list))
              (if success
                (mv T reduction)
                (contains-proof-or (rest stmt-list))))))

  (defun contains-proof-useforproof (useforproof-clause)
    (let ((rule (second useforproof-clause))
          (necessary-steps (cddr useforproof-clause)))
      (mv-let (success reduction)
              (contains-proof-and necessary-steps)
              (if success
                (mv T (cons rule reduction))
                (mv nil nil)))))

  (defun contains-proof-and (stmt-list)
    (if (null stmt-list)
      (mv T nil)
      (mv-let (success reduction)
              (contains-proof (first stmt-list))
              (if success
                (mv-let (success-tail reduction-tail)
                        (contains-proof-and (rest stmt-list))
                        (if success-tail
                          (mv T (cons reduction reduction-tail))
                          (mv nil nil)))
                (mv nil nil))))))

(defun prove-tree-base (output-file assumptions rules to-prove depth)
;  (prog2$ (my-cw output-file "Searching one more level down... in ~x0~%" to-prove) ; Uncomment and add a match parentheses if you want to see progress with search
  (let ((processed-tree (prove-tree output-file assumptions rules to-prove depth)))
    (if (null processed-tree)
      (mv nil nil)
      (mv-let (success result)
              (contains-proof processed-tree)
                (if success
                  (mv success result)
                  (if (< depth 1)
                    (mv nil nil)
                    (prove-tree-base output-file assumptions rules processed-tree (- depth 1))))))))

; Given a list of assumption names, construct a list of assumptions
(defun pull-assumptions (output-file names assumptions)
  (if (null names)
    nil
    (let ((found (assoc-equal (first names) assumptions)))
      (if (null found)
        (my-cw output-file "Could not find assumption ~x0, aborting.~%" (first names))
        (cons found (pull-assumptions output-file (rest names) assumptions))))))

(defun check-step (output-file assumptions rules rulesets step required depth)
  (let* ((step-name (first step))
         (step-concl (second step))
         (rule-list (third step))
         (given-subs (fourth step))
         (user-assump (fifth step))
         ; If assumptions are required or if the user has provided assumptions, pull them from the pool of assumptions
         (assumptions (if (or (member 'a required) (not (null user-assump))) (pull-assumptions output-file user-assump assumptions) assumptions)))
    (cond ((and (member 'a required) (not (equal (len user-assump) (len assumptions)))) nil) ; Fail if assumptions provided by user are invalid
          ((null rule-list) ; If no rule is specified, attempt to prove conclusion using any of the rules in the problem
           (mv-let (success proof-details)
                   (prove-stmt output-file assumptions rules step-concl given-subs required depth)
                   (if success
                     (report-success-base output-file step-name proof-details rulesets)
                     (if (or (null proof-details) (< depth 1))
                       (my-cw output-file "ERROR (step ~x0): Failed to prove conclusion ~x1 using any rule.~%" step-name (remove-quote step-concl))
                       (mv-let (success prove-tree-details)
                               (prove-tree-base output-file assumptions rules proof-details (- depth 1))
                               (if success
                                 (report-success-base output-file step-name prove-tree-details rulesets)
                                 (my-cw output-file "ERROR (step ~x0): Failed to prove conclusion ~x1 using any rule. Recursive search to depth ~x2 using rules without free variables also failed.~%" step-name (remove-quote step-concl) depth)))))))
          (T
            (let ((rule-info (get-rules rule-list rules)))
              (if (null rule-info)
                nil
                ; Attempt to prove conclusion using the specified rule
                (mv-let (success proof-details)
                        (prove-stmt output-file assumptions rule-info step-concl given-subs required depth)
                        (if success
                          (report-success-base output-file step-name proof-details rulesets)
                          (prog2$
                            (my-cw output-file "ERROR (step ~x0): Failed to prove conclusion ~x1 using the specified rule(s)" step-name (remove-quote step-concl))
                            (prog2$
                                (if (not (null given-subs))
                                  (my-cw output-file ", subs ~x0" given-subs)
                                  nil)
                                (prog2$
                                  (if (not (null user-assump))
                                    (my-cw output-file ", assumptions ~x0" assumptions)
                                    nil)
                                  (my-cw output-file ".~%"))))))))))))

; Recursively check the entire proof
(defun check-proof (output-file assumptions rules rulesets proof required depth)
  (if (null proof)
    T
    (and (check-step output-file assumptions rules rulesets (first proof) required depth)
         (check-proof output-file (cons (list (first (first proof)) (second (first proof))) assumptions) rules rulesets (rest proof) required depth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TOP-LEVEL FUNCTION ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-check (output-file assumptions rules rulesets proof constants required depth)
  (if (not (check-atoms output-file constants))
    (prog2$
      (my-cw output-file "ERROR: Invalid constants list.~%")
      nil)
    (let ((fmt-assumptions (prepare-assumptions output-file assumptions constants))
          (fmt-rules (prepare-rules output-file rules constants)))
      (if (not (verify-rulesets output-file rules rulesets))
        nil
        (let ((fmt-proof (prepare-proof output-file proof assumptions rules rulesets constants required))
              (fmt-required (prepare-required output-file required)))
          (cond ((and (null fmt-assumptions) assumptions)
                 (my-cw output-file "ERROR: Assumptions could not be validated.~%"))
                ((and (null fmt-rules) rules)
                 (my-cw output-file "ERROR: Rules could not be validated.~%"))
                ((and (null fmt-proof) proof)
                 (my-cw output-file "ERROR: Proof could not be validated.~%"))
                ((and (null fmt-required) required)
                 (my-cw output-file "ERROR: Required elements could not be validated.~%"))
                ((not (check-mappings output-file (append fmt-assumptions fmt-rules fmt-proof rulesets)))
                 (my-cw output-file "ERROR: Validation failed.~%"))
                ((and (not (null required)) (> depth 0))
                 (my-cw output-file "ERROR: Requirements list is non-empty, but search depth is non-zero.~%"))
                ((< depth 0)
                 (my-cw output-file "ERROR: Invalid search depth specified.~%"))
                (T (check-proof output-file fmt-assumptions fmt-rules rulesets fmt-proof fmt-required depth))))))))

(defun extract-second (list-of-lists)
  (if (null list-of-lists)
    nil
    (cons (second (first list-of-lists)) (extract-second (rest list-of-lists)))))

(defun verify-proof (output-file goal assumptions rules rulesets proof constants required depth)
  (let ((result (proof-check output-file assumptions rules rulesets proof constants required depth)))
    (if result
      ; Check if goal has been reached
      (if (member-equal goal (extract-second proof))
        (prog2$
          (my-cw output-file "RESULT: Congratulations! You have proved the goal.~%")
          T)
        (prog2$
          (my-cw output-file "RESULT: Proof was successful, but you have not proved the goal, ~x0.~%" goal)
          nil))
      (prog2$
        (my-cw output-file "RESULT: Proof failed.~%")
        nil))))
