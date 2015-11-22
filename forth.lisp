(defvar forth-registers
  '(pstack rstack pc
    dict compiling dtable))

(defstruct forth-word
  name prev immediate thread)

(defun forth-lookup (w last)
  (if last
      (if (eql (forth-word-name last) w)
          last
          (forth-lookup
           w (forth-word-prev last)))))

(defmacro forth-inner-interpreter ()
  `(loop
      do (cond
           ((functionp (car pc))
            (funcall (car pc)))
           ((consp (car pc))
            (push (cdr pc) rstack)
            (setf pc (car pc)))
           ((null pc)
            (setf pc (pop rstack)))
           (t
            (push (car pc) pstack)
            (setf pc (cdr pc))))
      until (and (null pc) (null rstack))))

(defvar forth-prim-forms nil)

(defmacro def-forth-naked-prim (&rest code)
  `(push ',code forth-prim-forms))

(defmacro def-forth-prim (&rest code)
  `(def-forth-naked-prim
       ,@code
       (setf pc (cdr pc))))
