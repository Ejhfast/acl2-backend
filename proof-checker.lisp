(in-package "ACL2")
(program)
(include-book "proof-formatter")
(include-book "my-cw")

;;; HELPER FUNCTIONS ;;;

; Returns the values corresponding to a given key
; Note: works for lists of lists in which the key is the first element (i.e. ((a b c)) has a mapping from a to (b c))
(defun get-value (key pairs)
  (let ((result (assoc-equal key pairs)))
    (if (null result)
      nil
      (rest result))))

; Get requirements or conclusions for rule
; Returns (mv rule-reqs rule-concl str-vars restrictions)
; Removes the "and" from rule-reqs, if it exists
(defun get-rule-info (output-file name rules)
  (let* ((rule-value (get-value name rules))
         (rule (first rule-value))
         (str-vars (second rule-value))
         (restrictions (third rule-value)))
    (cond ((null rule) 
           (prog2$
             (my-cw output-file "ERROR: No rule ~x0 found.~%" (remove-quote name))
             (mv nil nil nil nil)))
          ((not (equal (car rule) 'implies))
           (mv nil rule str-vars restrictions)) ; No requirements
          ((equal (caadr rule) 'and)
           (mv (cdadr rule) (caddr rule) str-vars restrictions)) ; More than one requirement, strip and
          (T
            (mv (list (second rule)) (third rule) str-vars restrictions))))) ; One requirement

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

; Check that the given substitutions obey the restrictions and do not substitute for a constant
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
  ; *** All methods in this mutual recursion return (mv success subs-used assumptions-used)

  ; After a successful partial unification:
  ; 1. If there any more unifications needed, attempt them.
  ; 2. If not, confirm the substitutions give us a successful result.
  (defun handle-success (output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required)
    (if (null rest-unifications)
      (confirm-subs output-file rule-reqs str-vars restrictions subs assumptions required)
      (match-lists output-file (first (first rest-unifications)) (second (first rest-unifications)) (rest rest-unifications) str-vars restrictions subs rule-reqs assumptions required)))

  ; Tries to unify the term and the pattern. Some substitutions may be provided already via subs.
  ; If everything is unified, it then checks that the given substitutions can cause the rule requirements
  ; to be fulfilled by statements in assumptions.
  ; Note that if this function is called with nil rule requirements, this function simply unifies the
  ; term and the pattern, and returns the list of substitutions used.
  (defun unify-check (output-file pattern term rest-unifications str-vars restrictions subs rule-reqs assumptions required)
    (if (atom pattern) ; Mapping here is unambiguous
      (if (member pattern (strip-cars subs)) ; If there is already a mapping
        (let ((match (get-value pattern subs)))
          (if (equal term match)
            (handle-success output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Matches previous mapping
            (mv nil nil nil))) ; Does not match previous mapping - fail
        (if (null pattern)
          (if (equal '(nil) term)
            (handle-success output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Both are nil
            (mv nil nil nil)) ; Cannot map something to nil - fail
          (if (member 's required)
            (prog2$
              (my-cw output-file "Substitutions are required; missing substitution for ~x0, aborting.~%" (remove-quote pattern))
              (mv nil nil nil))
            (let ((newsub (list (cons pattern term))))
              (if (check-subs newsub str-vars restrictions)
                (handle-success output-file rest-unifications str-vars restrictions (append subs newsub) rule-reqs assumptions required) ; Add substitution to current running list
                (mv nil nil nil)))))) ; New substitution would be invalid - fail
      (if (not (equal (len term) 1))
        (mv nil nil nil) ; Pattern is a list, but the term is not a list in a list
        (let ((term-list (first term))
              (pat-fn (ffn-symb pattern)))
          (if (eq 'quote pat-fn)
            (if (equal term-list pattern)
              (handle-success output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Quoted terms match exactly
              (mv nil nil nil)) ; Quoted term doesn't match - fail
            ; Regular function call
            (if (call-of pat-fn term-list)
              (match-lists output-file (fargs pattern) (fargs term-list) rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Both are function calls, attempt to unify their arguments
              (mv nil nil nil))))))) ; Function call didn't match - fail

  ; Decides how to appropriately call check-concl-sub-lst
  (defun match-lists (output-file patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required)
    (if (endp patterns)
      (if (endp terms)
        (handle-success output-file rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Both are nil (usually when list-matching completes)
        (mv nil nil nil)) ; Can't match nil with something else - fail
      (let ((match (assoc-eq (car patterns) subs)))
        (if match
          (if (>= (len terms) (len (cdr match)))
            (unify-check-lst output-file (len (cdr match)) (len (cdr match)) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Preexisting substitution fixes the number of terms that can be unified in the next step
            (mv nil nil nil)) ; No way to match according to the preexisting substitution - fail
          (if (member-eq (car patterns) str-vars)
            (unify-check-lst output-file 0 (len terms) patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; Next element in patterns is allowed to map to a string
            (if (equal (len terms) 0)
              (mv nil nil nil) ; Need to match to one term, but there are none left - fail
              (unify-check-lst output-file 1 1 patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required))))))) ; Next element in patterns must match to exactly one term
  
  ; Unify two lists. This is trivial unless strings are involved, in which case nummatch must iterate over all possible values.
  (defun unify-check-lst (output-file nummatch max patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required)
    (mv-let (head-terms tail-terms)
            (list-split nummatch terms)
            (mv-let (success new-subs assumptions-used)
                    (unify-check output-file (first patterns) head-terms (cons (list (rest patterns) tail-terms) rest-unifications) str-vars restrictions subs rule-reqs assumptions required) ; Unify the first element of the pattern with the appropriate subset of the terms
                    (if (null success)
                      (if (< nummatch max)
                        (unify-check-lst output-file (+ nummatch 1) max patterns terms rest-unifications str-vars restrictions subs rule-reqs assumptions required) ; If unification failed and you are allowed to match with more terms, unify the first element of the pattern with a longer term list
                        (mv nil nil nil)) ; Has failed all possible options - fail
                      (mv T new-subs assumptions-used))))) ; Successful - return

  ; Confirms that the substitutions found hold by searching for the necessary assumptions.
  ; TODO Remove method if actually unnecessary...
  (defun confirm-subs (output-file rule-reqs str-vars restrictions subs assumptions required)
    (find-assumptions output-file rule-reqs str-vars restrictions subs assumptions required))

  ; Searches the assumptions list for statements that can fit the rule requirements, taking the
  ; substitutions that have already been specified into account.
  (defun find-assumptions (output-file rule-reqs str-vars restrictions subs assumptions required)
    (if (and (member 'a required) (not (equal (len assumptions) (len rule-reqs))))
      (prog2$
        (my-cw output-file "~x0 assumptions are given, but there are ~x1 rule requirements. All assumptions must be provided exactly.~%" (len assumptions) (len rule-reqs))
        (mv nil nil nil))
      (find-assumptions-sub output-file rule-reqs str-vars restrictions subs assumptions assumptions required))) ; Search for rule requirements

  ; Subroutine -- attempts to unify the first rule with the first assumption left to check, continuing as appropriate.
  (defun find-assumptions-sub (output-file rule-reqs str-vars restrictions given-subs assumptions-left assumptions required)
    (if (null rule-reqs)
      (mv T given-subs nil) ; Nothing left to prove
      (if (null assumptions-left)
        (mv nil nil nil) ; Can't find assumption - fail
        (let ((test-assumption (cdr (first assumptions-left))))
          (mv-let (success subs discarded)
                  (unify-check output-file (first rule-reqs) test-assumption nil str-vars restrictions given-subs nil nil required) ; Try to unify the first rule requirement with the first assumption (do no further checking)
                  (declare (ignore discarded))
                  (if (null success)
                    (if (member 'a required)
                      (mv nil nil nil) ; Should match one-to-one
                      (find-assumptions-sub output-file rule-reqs str-vars restrictions given-subs (rest assumptions-left) assumptions required)) ; Try this with a different assumption
                    (let ((assumptions (if (member 'a required) (rest assumptions) assumptions)))
                      (mv-let (rest-success rest-subs assumptions-used)
                              (find-assumptions-sub output-file (rest rule-reqs) str-vars restrictions subs assumptions assumptions required) ; Continue trying to find the rest of the rule requirements
                              (if rest-success
                                (mv T rest-subs (cons (car (first assumptions-left)) assumptions-used)) ; Add the assumption used for this stage to the front of the list of assumptions used
                                (if (member 'a required)
                                  (mv nil nil nil) ; No alternative - assumptions should match one-to-one
                                  (find-assumptions-sub output-file rule-reqs str-vars restrictions given-subs (rest assumptions-left) assumptions required)))))))))))) ; Try a different assumption to fit the rule requirement

; Check if the given substitutions are valid, then attempt to unify the given conclusion with the given rule
; Returns (mv success subs-used assumptions-used)
(defun check-concl (output-file rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions required)
  (if (check-subs given-subs str-vars restrictions)
    (unify-check output-file rule-concl (list step-concl) nil str-vars restrictions given-subs rule-reqs assumptions required) ; Attempt to unify the conclusion of the step with the conclusion of the rule
    (mv nil nil nil))) ; Invalid subs - fail

; Attempt to prove the given conclusion with the available rules and assumptions
(defun prove-stmt (output-file assumptions rules step-concl given-subs required)
  (if (null rules)
    (mv nil nil nil nil) ; No rules left - fails
    (let* ((rule-used (first (first rules)))) ; Name of rule used - start by using the first rule
      (mv-let (rule-reqs rule-concl str-vars restrictions)
              (get-rule-info output-file rule-used rules)
              (if (and (member 'a required) (not (equal (len assumptions) (len rule-reqs))))
                (prog2$
                  (my-cw output-file "~x0 assumptions are given, but there are ~x1 rule requirements. All assumptions must be provided exactly.~%" (len assumptions) (len rule-reqs))
                  (mv nil nil nil nil))
                (mv-let (success subs assumptions-used)
                        (check-concl output-file rule-concl step-concl str-vars restrictions given-subs rule-reqs assumptions required) ; Attempt to prove statement by using the first rule
                        (if success
                          (mv T rule-used subs assumptions-used) ; Return the results
                          (prove-stmt output-file assumptions (rest rules) step-concl given-subs required)))))))) ; If it didn't work, try with a different rule

; Given a list of assumption names, construct a list of assumptions
(defun pull-assumptions (output-file names assumptions)
  (if (null names)
    nil
    (let ((found (assoc-equal (first names) assumptions)))
      (if (null found)
        (my-cw output-file "Could not find assumption ~x0, aborting.~%" (first names))
        (cons found (pull-assumptions output-file (rest names) assumptions))))))

; Check one step in the proof
(defun check-step (output-file assumptions rules step required)
  (let* ((step-name (first step))
        (step-concl (second step))
        (rule (third step))
        (given-subs (fourth step))
        (user-assump (fifth step))
        (assumptions (if (or (member 'a required) (not (null user-assump))) (pull-assumptions output-file user-assump assumptions) assumptions)))
    (cond ((and (member 'a required) (not (equal (len user-assump) (len assumptions)))) nil) ; Fail if assumptions provided by user turn out to be invalid
          ((and (null rule) (member 'r required)) (my-cw output-file "ERROR (step ~x0): No rule was named, but you are required to name rules.~%" step-name))
          ((null rule)
           (mv-let (success rule-used subs assumptions-used)
                (prove-stmt output-file assumptions rules step-concl given-subs required) ; Attempt to prove conclusion using one of the rules in the problem
                (if success
                  (prog2$
                    (my-cw output-file "Step ~x0: Successfully proved ~x1 using rule ~x2 with substitutions ~x3 and assumptions ~x4.~%" step-name (remove-quote step-concl) rule-used (remove-quote-alist subs) assumptions-used)
                    T)
                  (prog2$
                    (my-cw output-file "ERROR (step ~x0): Failed to prove conclusion ~x1 using any rule.~%" step-name (remove-quote step-concl))
                    nil))))
          (T
            (let ((rule-info (assoc-equal rule rules)))
              (if (null rule-info)
                (my-cw output-file "ERROR (step ~x0): Rule ~x1 not found.~%" step-name rule)
                (mv-let (success rule-used subs assumptions-used)
                        (prove-stmt output-file assumptions (list rule-info) step-concl given-subs required) ; Attempt to prove conclusion using the named rule
                        (if success
                          (prog2$
                            (my-cw output-file "Step ~x0: Successfully proved ~x1 using rule ~x2 with substitutions ~x3 and assumptions ~x4.~%" step-name (remove-quote step-concl) rule-used (remove-quote-alist subs) assumptions-used)
                            T)
                          (prog2$
                            (my-cw output-file "ERROR (step ~x0): Failed to prove conclusion ~x1 using rule ~x2" step-name (remove-quote step-concl) rule)
                            (prog2$
                              (if (not (null given-subs)) ; If substitutions were named, list them in the error message
                                (my-cw output-file ", subs ~x0" given-subs)
                                nil)
                              (prog2$
                                (if (not (null user-assump)) ; If assumptions were named, list them in the error message
                                  (my-cw output-file ", assumptions ~x0" assumptions)
                                  nil)
                                (my-cw output-file ".~%"))))))))))))

; Recursively check the entire proof
  (defun check-proof (output-file assumptions rules proof required)
  (if (null proof)
    T
    (and (check-step output-file assumptions rules (first proof) required)
         (check-proof output-file (cons (list (first (first proof)) (second (first proof))) assumptions) rules (rest proof) required))))

;;; TOP-LEVEL FUNCTION ;;;
(defun proof-check (output-file assumptions rules proof constants required)
  (if (not (check-atoms output-file constants))
    (prog2$
      (my-cw output-file "ERROR: Invalid constants list.~%")
      nil)
    (let ((fmt-assumptions (prepare-assumptions output-file assumptions constants))
          (fmt-rules (prepare-rules output-file rules constants))
          (fmt-proof (prepare-proof output-file proof constants))
          (fmt-required (prepare-required output-file required)))
      (cond ((and (null fmt-assumptions) assumptions)
             (prog2$
               (my-cw output-file "ERROR: Assumptions could not be validated.~%")
               nil))
            ((and (null fmt-rules) rules)
             (prog2$
               (my-cw output-file "ERROR: Rules could not be validated.~%")
               nil))
            ((and (null fmt-proof) proof)
             (prog2$
               (my-cw output-file "ERROR: Proof could not be validated.~%")
               nil))
            ((and (null fmt-required) required)
             (prog2$
               (my-cw output-file "ERROR: Required elements could not be validated.~%")
               nil))
            ((not (check-mappings output-file (append fmt-assumptions fmt-rules fmt-proof)))
             (prog2$
               (my-cw output-file "ERROR: Validation failed.~%")
               nil))
            (T
             (if (check-proof output-file fmt-assumptions fmt-rules fmt-proof fmt-required)
               (prog2$
                 (my-cw output-file "RESULT: PROOF SUCCEEDED.~%")
                 T)
               (prog2$
                 (my-cw output-file "RESULT: PROOF FAILED.~%")
                 nil)))))))
