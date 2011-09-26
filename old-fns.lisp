; Substitution functions
(mutual-recursion
  (defun my-sublis-var-lst (alist l)
    (declare (xargs :measure (acl2-count l)
                    :guard (and (symbol-alistp alist)
                                (pseudo-term-listp l))))
    (if (endp l)
      nil
      (let ((subbed (my-sublis-var alist (car l))))
        (append subbed (my-sublis-var-lst alist (cdr l))))))

  (defun my-sublis-var (alist form)
    (declare (xargs :measure (acl2-count form)
                    :guard (and (symbol-alistp alist)
                                (pseudo-termp form))))
    (cond ((variablep form)
           (let ((a (assoc-eq form alist)))
             (cond (a (cdr a))
                   (t (list form)))))
          ((fquotep form) (list form))
          (t (list (cons
                     (ffn-symb form)
                     (my-sublis-var-lst alist (fargs form))))))))

; Pull a list of all variables from a term
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

; Make substitutions in tosub according to sublist.
(defun make-subst (sublist tosub)
  (if (null tosub)
    nil
    (let ((vars (get-vars-from-term tosub))
          (keys (strip-cars sublist)))
      (prog2$
        (let ((diff (set-difference-equal vars keys)))
          (if diff
            (cw "WARNING: Some variables in the rule were not explicitly substituted for (did you forget to specify a constant?). These have been implicitly substituted as themselves: ~x0.~%" diff)
            T))
        (let ((result (my-sublis-var sublist tosub)))
          (if (<= (len result) 1)
            (first result)
            (prog2$
              (cw "INTERNAL ERROR: Result of substitution should have had 0 or 1 elements, but it had ~x0.~%" (len result))
              nil)))))))

(defun make-subst-lst (sublist tosub)
  (if (null tosub)
    nil
    (let ((vars (get-vars-from-term tosub))
          (keys (strip-cars sublist)))
      (prog2$
        (let ((diff (set-difference-equal vars keys)))
          (if diff
            (cw "WARNING: Some variables in the rule were not explicitly substituted for (did you forget to specify a constant?). These have been implicitly substituted as themselves: ~x0.~%" diff)
            T))
        (my-sublis-var-lst sublist tosub)))))


