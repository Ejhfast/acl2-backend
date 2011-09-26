(defun mem (e x)
  (if (consp x)
    (if (equal e (car x))
      t
      (mem e (cdr x)))
    nil))

(defun fact (n)
  (if (equal n 0)
    1
    (* n (fact (- n 1)))))

(defun flip (p)
  (if (consp p)
    (cons (cdr p) (car p))
    nil))

(defun flip-list (x)
  (if (consp x)
    (cons (flip (car x)) (flip-list (cdr x)))
    nil))

(defun swap (x)
  ; Flip every cons pair in a binary tree
  (if (consp x)
    (cons (swap (cdr x)) (swap (car x)))
    x))

(defun size (x)
  ; Count the number of leaves in a binary tree
  (if (consp x)
    (+ (size (car x)) (size (cdr x)))
    1))

(defun depth (x)
  ; Compute the length of the longest branch in a binary tree
  (if (consp x)
    (+ 1 (max (depth (car x)) (depth (cdr x))))
    0))

(defun tsubst (x y z)
  ; Substitute x for each occurrence of y in the binary tree z.
;  (if (equal y z)
;    x
;    (if (consp z)
;      (cons (tsubst x y (car z)) (tsubst x y (cdr z)))
;      z)))
  (cond ((equal y z) x)
        ((consp z) (cons (tsubst x y (car z)) (tsubst x y (cdr z))))
        (T z)))
