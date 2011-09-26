(in-package "ACL2")
(program)
(include-book "proof-formatter")

;;; HELPER FUNCTIONS ;;;

; Returns the values corresponding to a given key
; Note: works for lists in which the key is the first element
(defun get-value (key pairs)
  (let ((result (assoc-equal key pairs)))
    (if (null result)
      nil
      (rest result))))

; Get requirements or conclusions for rule
; Returns (mv rule-reqs rule-concl str-vars)
; Removes the "and" from rule-reqs, if it exists
(defun get-rule-info (name rules)
  (let* ((rule-value (get-value name rules))
         (rule (car rule-value))
         (str-vars (cadr rule-value))
         (restrictions (caddr rule-value)))
    (cond ((null rule) 
           (prog2$
             (cw "ERROR: No rule ~x0 found.~%" name)
             (mv nil nil nil nil)))
          ((not (equal (car rule) 'implies))
           (mv nil rule str-vars restrictions)) ; No requirements
          ((equal (caadr rule) 'and)
           (mv (cdadr rule) (caddr rule) str-vars restrictions)) ; More than one requirement, strip and
          (T
            (mv (list (cadr rule)) (caddr rule) str-vars restrictions))))) ; One requirement

(defun list-split (nummatch terms)
  (if (equal nummatch 0)
    (mv nil terms)
    (mv-let (head tail)
            (list-split (- nummatch 1) (cdr terms))
            (mv (cons (car terms) head) tail))))

(defun check-number (wrapped)
  (if (equal (len wrapped) 1)
    (let ((x (first wrapped)))
      (and (not (atom x)) (equal (len x) 2) (equal (first x) 'quote) (acl2-numberp (second x))))
    nil))

(defun check-string (wrapped)
  (if (equal (len wrapped) 1)
    (let ((x (first wrapped)))
      (and (not (atom x)) (equal (len x) 2) (equal (first x) 'quote) (stringp (second x))))
    nil))

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

(defmacro call-of (fn term)
  `(and (consp ,term)
        (eq ,fn (ffn-symb ,term))))
(defmacro empty-alist () nil)

(mutual-recursion
  ; TODO Change name >_>
  (defun handle-success (rest-unifications str-vars restrictions subs rule-reqs assumptions)
    (if (null rest-unifications)
      (confirm-subs rule-reqs str-vars restrictions subs assumptions)
      (match-lists (first (first rest-unifications)) (second (first rest-unifications)) (rest rest-unifications) str-vars restrictions subs rule-reqs assumptions)))

  ; Tries to unify the term and the pattern. Some substitutions may be provided already via subs.
  ; If everything is unified, it then checks that the given substitutions can cause the rule requirements
  ; to be fulfilled by statements in assumptions.
  ; Note that if this function is called with nil rule requirements, this function simply unifies the
  ; term and the pattern, and returns the list of substitutions used.
  ; Returns (mv success subs-used)
  (defun unify-check (pattern term rest-unifications str-vars restrictions subs rule-reqs assumptions)
    (if (atom pattern) ; Mapping here is unambiguous
      (if (member pattern (strip-cars subs)) ; If there is already a mapping
        (let ((match (get-value pattern subs)))
          (if (equal term match)
            (handle-success rest-unifications str-vars restrictions subs rule-reqs assumptions)
            (mv nil nil))) ; Does not match previous mapping
        (if (null pattern)
          (if (equal '(nil) term)
            (handle-success rest-unifications str-vars restrictions subs rule-reqs assumptions)
            (mv nil nil)) ; Cannot map something to nil
          (let ((newsub (list (cons pattern term))))
            (if (check-subs newsub str-vars restrictions)
              (handle-success rest-unifications str-vars restrictions (append subs newsub) rule-reqs assumptions)
              (mv nil nil)))))
      (if (not (equal (len term) 1)) ; If the pattern is a list, the term must be a list in a list
          (mv nil nil)
        (let ((term-list (first term))
              (pat-fn (ffn-symb pattern)))
          (if (eq 'quote pat-fn)
            (if (equal term-list pattern)
              (handle-success rest-unifications str-vars restrictions subs rule-reqs assumptions)
              (mv nil nil)) ; Quoted term doesn't match
            ; Regular function call
            (if (call-of pat-fn term-list)
              (match-lists (fargs pattern) (fargs term-list) rest-unifications str-vars restrictions subs rule-reqs assumptions)
              (mv nil nil))))))) ; Function call didn't match

  ; Decides how to appropriately call check-concl-sub-lst
  (defun match-lists (patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)
    (if (endp patterns)
      (if (endp terms)
        (handle-success rest-unifications str-vars restrictions subs rule-reqs assumptions)
        (mv nil nil)) ; Can't match nil with something else
      (let ((match (assoc-eq (car patterns) subs)))
        (if match
          (if (>= (len terms) (len (cdr match)))
            (unify-check-lst (len (cdr match)) (len (cdr match)) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)
            (mv nil nil)) ; No way to match according to the preexisting substitution
          (if (member-eq (car patterns) str-vars)
            (unify-check-lst 0 (len terms) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)
            (if (equal (len terms) 0)
              (mv nil nil) ; Need to match to one term, but there are none left
              (unify-check-lst 1 1 patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)))))))
  
  (defun unify-check-lst (nummatch max patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)
    (if (endp patterns)
      (if (endp terms)
        (mv T subs)
        (mv nil nil)) ; Can't match nil with something else
      (mv-let (head-terms tail-terms)
              (list-split nummatch terms)
              (mv-let (success new-subs)
                      (unify-check (first patterns) head-terms (cons (list (rest patterns) tail-terms) rest-unifications) str-vars restrictions subs rule-reqs assumptions)
                      (if (null success)
                        (if (< nummatch max)
                          (unify-check-lst (+ nummatch 1) max patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions)
                          (mv nil nil))
                        (mv T new-subs))))))

  ; Confirms that the substitutions found hold by searching for the necessary assumptions.
  (defun confirm-subs (rule-reqs str-vars restrictions subs assumptions)
    (find-assumptions rule-reqs str-vars restrictions subs assumptions))

  ; Searches the assumptions list for statements that can fit the rule requirements, taking the
  ; substitutions that have already been specified into account
  (defun find-assumptions (rule-reqs str-vars restrictions subs assumptions)
    (let ((assumption-stmts (strip-cdrs assumptions)))
      (if (null rule-reqs)
        (mv T subs)
        (find-assumptions-sub rule-reqs str-vars restrictions subs assumption-stmts assumption-stmts))))

  ; Subroutine -- attempts to unify the first rule with the first assumption left to check, continuing as appropriate.
  (defun find-assumptions-sub (rule-reqs str-vars restrictions given-subs assumptions-left assumptions)
    (if (null rule-reqs)
      (mv T given-subs)
      (if (null assumptions-left)
        (mv nil nil)
        (mv-let (success subs)
                  (unify-check (first rule-reqs) (first assumptions-left) nil str-vars restrictions given-subs nil nil) ; Try to unify the first rule requirement with the first assumption (do no further checking)
                (if (null success)
                  (find-assumptions-sub rule-reqs str-vars restrictions given-subs (rest assumptions-left) assumptions) ; Try this with a different assumption
                  (mv-let (rest-success rest-subs)
                          (find-assumptions-sub (rest rule-reqs) str-vars restrictions subs assumptions assumptions) ; Continue trying to find the rest of the rule requirements
                          (if rest-success
                            (mv T rest-subs)
                            (find-assumptions-sub rule-reqs str-vars restrictions given-subs (rest assumptions-left) assumptions)))))))))

(defun check-concl (rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions)
  (if (check-subs given-subs str-vars restrictions)
    (unify-check rule-concl (list step-concl) nil str-vars restrictions given-subs rule-reqs assumptions)
    (mv nil nil)))

(defun check-rules (assumptions rules step-concl given-subs)
  (if (null rules)
    (mv nil nil nil) ; No rules left
    (let* ((rule-used (first (first rules)))) ; Name of rule used
      (mv-let (rule-reqs rule-concl str-vars restrictions)
              (get-rule-info rule-used rules)
              (mv-let (success subs)
                      (check-concl rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions)
                      (if success
                        (mv T rule-used subs)
                        (check-rules assumptions (rest rules) step-concl given-subs)))))))

; Check one step in the proof
(defun check-step (assumptions rules step)
  (let ((step-name (first step))
        (step-concl (second step))
        (rule (third step))
        (given-subs (fourth step)))
    (if (null rule)
      (mv-let (success rule-used subs)
              (check-rules assumptions rules step-concl given-subs)
              (if success
                (prog2$
                  (cw "Step ~x0: Successfully proved ~x1 using rule ~x2 with substitutions ~x3.~%" step-name step-concl rule-used subs)
                  T)
                (prog2$
                  (cw "ERROR (step ~x0): Failed to prove conclusion ~x1 using any rule.~%" step-name step-concl)
                  nil)))
      (let ((rule-info (assoc-equal rule rules)))
        (mv-let (success rule-used subs)
                (check-rules assumptions (list rule-info) step-concl given-subs)
                (if success
                  (prog2$
                    (cw "Step ~x0: Successfully proved ~x1 using rule ~x2 with substitutions ~x3.~%" step-name step-concl rule-used subs)
                    T)
                  (prog2$
                    (cw "ERROR (step ~x0): Failed to prove conclusion ~x1 using rule ~x2.~%" step-name step-concl rule)
                    nil)))))))

; Recursively check the entire proof
(defun check-proof (assumptions rules proof)
  (if (null proof)
    T
    (and (check-step assumptions rules (first proof))
         (check-proof (cons (list (first (first proof)) (second (first proof))) assumptions) rules (rest proof)))))

;;; TOP-LEVEL FUNCTION ;;;
(defun proof-check (assumptions rules proof constants)
  (if (not (check-atoms constants))
    (prog2$
      (cw "ERROR: Invalid constants list.~%")
      nil)
    (let ((fmt-assumptions (prepare-assumptions assumptions constants))
          (fmt-rules (prepare-rules rules constants))
          (fmt-proof (prepare-proof proof constants)))
      (cond ((and (null fmt-assumptions) assumptions)
             (prog2$
               (cw "ERROR: Assumptions could not be validated.~%")
               nil))
            ((and (null fmt-rules) rules)
             (prog2$
               (cw "ERROR: Rules could not be validated.~%")
               nil))
            ((and (null fmt-proof) proof)
             (prog2$
               (cw "ERROR: Proof could not be validated.~%")
               nil))
            ((not (check-mappings (append fmt-assumptions fmt-rules fmt-proof)))
             (prog2$
               (cw "ERROR: Validation failed.~%")
               nil))
            (T
             (if (check-proof fmt-assumptions fmt-rules fmt-proof)
               (prog2$
                 (cw "RESULT: PROOF SUCCEEDED.~%")
                 T)
               (prog2$
                 (cw "RESULT: PROOF FAILED.~%")
                 nil)))))))
