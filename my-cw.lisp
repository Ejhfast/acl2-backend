; This file defines the utility my-cw, which writes to the end of the indicated
; file, creating the file if it does not already exist. If the filename is null,
; prints to the console instead of writing to a file (behaves like cw).

; General form:
; (my-cw filename fmt-string arg1 arg2 ... argn)

; Examples:
; (my-cw "my-cw-output.txt" "First line.~%")
; (my-cw "my-cw-output.txt" "Second line has ~x0 and ~x1.~%" 'a 'b)

; Certify with:
; (certify-book "my-cw" 0 t :ttags (:my-cw))

(in-package "ACL2")

  (defun my-fmt-to-comment-window (str alist col evisc-tuple filename)
   (declare (ignore str alist col evisc-tuple filename)
    (xargs :guard t))
   nil)

  ; We need a trust tag because of the use of raw-mode in the progn! below,
  (defttag :my-cw)

  ; Now smash the definition of the above function, using raw-mode.
  (progn!
   (set-raw-mode-on state)
   (defun my-fmt-to-comment-window (str alist col evisc-tuple filename)
    (with-open-file
     (*terminal-io* filename
      :direction :output
      :if-exists :append
      :if-does-not-exist :create)
     (fmt-to-comment-window str alist col evisc-tuple))))

  ; The following definition is based on the definition of cw.
  (defmacro my-cw (filename str &rest args)
   `(if (null ,filename)
     (fmt-to-comment-window ,str
      (pairlis2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
       (list ,@args)) 0 nil)
     (my-fmt-to-comment-window ,str
      (pairlis2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
       (list ,@args)) 0 nil ,filename)))
