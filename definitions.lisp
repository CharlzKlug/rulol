(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun flatten (x)
    (labels ((rec (x acc)
	       (cond ((null x) acc)
		     ((atom x) (cons x acc))
		     (t (rec
			 (car x)
			 (rec (cdr x) acc))))))
      (rec x nil)))

  (defun g!-symbol-p (s)
    (and (symbolp s)
	 (> (length (symbol-name s)) 2)
	 (string= (symbol-name s)
		  "G!"
		  :start1 0
		  :end1 2)))

  (defun mkstr (&rest args)
    (with-output-to-string (s)
      (dolist (a args) (princ a s))))

  (defun symb (&rest args)
    (values (intern (apply #'mkstr args))))

  (defun o!-symbol-p (s)
    (and (symbolp s)
	 (> (length (symbol-name s)) 2)
	 (string= (symbol-name s)
		  "O!"
		  :start1 0
		  :end1 2)))

  (defun o!-symbol-to-g!-symbol (s)
    (symb "G!"
	  (subseq (symbol-name s) 2)))

  (defun segment-reader (stream ch n)
    (if (> n 0)
	(let ((chars))
	  (do ((curr (read-char stream)
		     (read-char stream)))
	      ((char= ch curr))
	    (push curr chars))
	  (cons (coerce (nreverse chars) 'string)
		(segment-reader stream ch (- n 1))))))

  (defun group (source n)
    (if (zerop n) (error "zero length"))
    (labels ((rec (source acc)
	       (let ((rest (nthcdr n source)))
		 (if (consp rest)
		     (rec rest (cons
				(subseq source 0 n)
				acc))
		     (nreverse
		      (cons source acc))))))
      (if source (rec source nil) nil)))
  (defun defunits-chaining% (u units)
  (let ((spec (find u units :key #'car)))
    (if (null spec)
	(error "Unknown unit ~a" u)
	(let ((chain (cadr spec)))
	  (if (listp chain)
	      (* (car chain)
		 (defunits-chaining%
		     (cadr chain)
		     units))
	      chain)))))

  (defun defunits-chaining (u units prev)
  (if (member u prev)
      (error "~{ ~a~^ depends on~}"
	     (cons u prev)))
  (let ((spec (find u units :key #'car)))
    (if (null spec)
	(error "Unknown unit ~a" u)
	(let ((chain (cadr spec)))
	  (if (listp chain)
	      (* (car chain)
		 (defunits-chaining
		     (cadr chain)
		     units
		   (cons u prev)))
	      chain)))))

  (defun tree-leaves% (tree result)
    (if tree
	(if (listp tree)
	    (cons
	     (tree-leaves% (car tree)
			   result)
	     (tree-leaves% (cdr tree)
			   result))
	    result)))

  
  (defun predicate-splitter (orderp splitp)
    (lambda (a b)
      (let ((s (funcall splitp a)))
	(if (eq s (funcall splitp b))
	    (funcall orderp a b)
	    s))))

  
(defun tree-leaves%% (tree test result)
  (if tree
      (if (listp tree)
	  (cons
	   (tree-leaves%% (car tree) test result)
	   (tree-leaves%% (cdr tree) test result))
	  (if (funcall test tree)
	      (funcall result tree)
	      tree))))

)

(defmacro defmacro! (name args &rest body)
  (let* ((os (remove-if-not #'o!-symbol-p args))
	 (gs (mapcar #'o!-symbol-to-g!-symbol os)))
    `(defmacro/g! ,name ,args
       `(let ,(mapcar #'list (list ,@gs) (list ,@os))
	  ,(progn ,@body)))))

(defmacro defmacro/g! (name args &rest body)
  (let ((syms (remove-duplicates
	       (remove-if-not #'g!-symbol-p
			      (flatten body)))))
    `(defmacro ,name ,args
       (let ,(mapcar
	      (lambda (s)
		`(,s (gensym ,(subseq
			       (symbol-name s)
			       2))))
	      syms)
	 ,@body))))

;#+cl-ppcre
(defmacro! match-mode-ppcre-lambda-form (o!args)
  ``(lambda (,',g!str)
      (cl-ppcre:scan
       ,(car ,g!args)
       ,',g!str)))

;#+cl-ppcre
(defmacro! subst-mode-ppcre-lambda-form (o!args)
  ``(lambda (,',g!str)
      (cl-ppcre:regex-replace-all
       ,(car ,g!args)
       ,',g!str
       ,(cadr ,g!args))))

;#+cl-ppcre
(defun |#~-reader| (stream sub-char numarg)
  (declare (ignore sub-char numarg))
  (let ((mode-char (read-char stream)))
    (cond
      ((char= mode-char #\m)
       (match-mode-ppcre-lambda-form
	(segment-reader stream
			(read-char stream)
			1)))
      ((char= mode-char #\s)
       (subst-mode-ppcre-lambda-form
	(segment-reader stream
			(read-char stream)
			2)))
      (t (error "Unknown #~~ mode character")))))

;#+cl-ppcre
(set-dispatch-macro-character #\# #\~ #'|#~-reader|)

(defun cyclic-p-aux (l seen)
  (if (consp l)
      (or (gethash l seen)
	  (progn
	    (setf (gethash l seen) t)
	    (or (cyclic-p-aux (car l) seen)
		(cyclic-p-aux (cdr l) seen))))))

(defun cyclic-p (l)
  (cyclic-p-aux l (make-hash-table)))

(defvar safe-read-from-string-blacklist
  '(#\# #\: #\|))

(let ((rt (copy-readtable nil)))
  (defun safe-reader-error (stream closech)
    (declare (ignore stream closech))
    (error "safe-read-from-string failure"))
  (dolist (c safe-read-from-string-blacklist)
    (set-macro-character
     c #'safe-reader-error nil rt))
  (defun safe-read-from-string (s &optional fail)
    (if (stringp s)
	(let ((*readtable* rt) *read-eval*)
	  (handler-bind
	      ((error (lambda (condition)
			(declare (ignore condition))
			(return-from
			 safe-read-from-string fail))))
	    (read-from-string s)))
	fail)))

(defmacro unit-of-time (value unit)
  `(* ,value
      ,(case unit
	     ((s) 1)
	     ((m) 60)
	     ((h) 3600)
	     ((d) 86400)
	     ((ms) 1/1000)
	     ((us) 1/1000000))))

(defmacro! defunits% (quantity base-unit &rest units)
  `(defmacro ,(symb 'unit-of- quantity) (,g!val ,g!un)
     `(* ,,g!val
	 ,(case ,g!un
		((,base-unit) 1)
		,@(mapcar (lambda (x)
			    `((,(car x)) ,(cadr x)))
			  (group units 2))))))


(defmacro! defunits%% (quantity base-unit &rest units)
  `(defmacro ,(symb 'unit-of- quantity) (,g!val ,g!un)
     `(* ,,g!val
	 ,(case ,g!un
		((,base-unit) 1)
		,@(mapcar (lambda (x)
			    `((,(car x))
			      ,(defunits-chaining%
				(car x)
				(cons `(,base-unit 1)
				      (group units 2)))))
			  (group units 2))))))



(defmacro! defunits (quantity base-unit &rest units)
  `(defmacro ,(symb 'unit-of- quantity)
       (,g!val ,g!un)
     `(* ,,g!val
	 ,(case ,g!un
		((,base-unit) 1)
		,@(mapcar (lambda (x)
			    `((,(car x))
			      ,(defunits-chaining
				(car x)
				(cons
				 `(,base-unit 1)
				 (group units 2))
				nil)))
			  (group units 2))))))

(defunits distance m
  km 1000
  cm 1/100
  mm (1/10 cm)
  nm (1/1000 mm)

  yard 9144/10000 ; Принято в 1956
  foot (1/3 yard)
  inch (1/12 foot)
  mile (1760 yard)
  furlong (1/8 mile)

  fathom (2 yard) ; Принято в 1929
  nautical-mile 1852
  cable (1/10 nautical-mile)
  
  old-brit-nautical-mile ; Отменено в 1970
  (6080/3 yard)
  old-brit-cable
  (1/10 old-brit-nautical-mile)
  old-brit-fathom
  (1/100 old-brit-cable))

(defmacro tree-leaves (tree test result)
  `(tree-leaves%%
    ,tree
    (lambda (x)
      (declare (ignorable x))
      ,test)
    (lambda (x)
      (declare (ignorable x))
      ,result)))