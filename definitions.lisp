(eval-when (:compile-toplevel :load-toplevel :execute)
  (ql:quickload "cl-ppcre")
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
  (defvar cxr-inline-thresh 10)

  (defun let-binding-transform (bs)
    (if bs
	(cons
	 (cond ((symbolp (car bs))
		(list (car bs)))
	       ((consp (car bs))
		(car bs))
	       (t
		(error "Bad let bindings")))
	 (let-binding-transform (cdr bs))))))

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
	fail))

  (defun pandoriclet-get (letargs)
    `(case sym
       ,@(mapcar #`((,(car a1)) ,(car a1))
		 letargs)
       (t (error
	   "Unknown pandoric get: ~a"
	   sym))))

  (defun pandoriclet-set (letargs)
    `(case sym
       ,@(mapcar #`((,(car a1))
		    (setq ,(car a1) val))
		 letargs)
       (t (error
	   "Unknown pandoric set: ~a"
	   sym val)))))

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

(defmacro! nlet-tail (n letargs &rest body)
  (let ((gs (loop for i in letargs
	       collect (gensym))))
    `(macrolet
	 ((,n ,gs
	    `(progn
	       (psetq
		,@(apply #'nconc
			 (mapcar
			  #'list
			  ',(mapcar #'car letargs)
			  (list ,@gs))))
	       (go ,',g!n))))
       (block ,g!b
	 (let ,letargs
	   (tagbody
	      ,g!n (return-from
		    ,g!b (progn ,@body))))))))

(defun nlet-tail-fact (n)
  (nlet-tail fact ((n n) (acc 1))
	     (if (zerop n)
		 acc
		 (fact (- n 1) (* acc n)))))

(defmacro cxr% (x tree)
  (if (null x)
      tree
      `(,(cond
	  ((eq 'a (cadr x)) 'car)
	  ((eq 'd (cadr x)) 'cdr)
	  (t (error "Non A/D symbol")))
	 ,(if (= 1 (car x))
	      `(cxr% ,(cddr x) ,tree)
	      `(cxr% ,(cons (- (car x) 1) (cdr x))
		     ,tree)))))

(defun eleventh (x)
  (cxr% (1 a 10 d) x))



(defmacro! cxr (x tree)
  (if (null x)
      tree
      (let ((op (cond
		  ((eq 'a (cadr x)) 'car)
		  ((eq 'd (cadr x)) 'cdr)
		  (t (error "Non A/D symbol")))))
	(if (and (integerp (car x))
		 (<= 1 (car x) cxr-inline-thresh))
	    (if (= 1 (car x))
		`(,op (cxr ,(cddr x) ,tree))
		`(,op (cxr ,(cons (- (car x) 1) (cdr x))
			   ,tree)))
	    `(nlet-tail
	      ,g!name ((,g!count ,(car x))
		       (,g!val (cxr ,(cddr x) ,tree)))
	      (if (>= 0 ,g!count)
		  ,g!val
		  ;; Будет хвостом:
		  (,g!name (- ,g!count 1)
			   (,op ,g!val))))))))

(defun nthcdr% (n list)
  (cxr (n d) list))

(defun nth% (n list)
  (declare (ignorable n list))
  (cxr (1 a n d) list))

(defmacro def-english-list-accessors (start end)
  (if (not (<= 1 start end))
      (error "Bad start/end range"))
  `(progn
     ,@(loop for i from start to end collect
	    `(defun
		 ,(symb
		   (map 'string
			(lambda (c)
			  (if (alpha-char-p c)
			      (char-upcase c)
			      #\-))
			(format nil "~:r" i)))
		 (arg)
	       (cxr (1 a ,(- i 1) d) arg)))))

(defun cxr-calculator (n)
  (loop for i from 1 to n
     sum (expt 2 i)))

(defun cxr-symbol-p (s)
  (if (symbolp s)
      (let ((chars (coerce
		    (symbol-name s)
		    'list)))
	(and
	 (< 6 (length chars))
	 (char= #\C (car chars))
	 (char= #\R (car (last chars)))
	 (null (remove-if
		(lambda (c)
		  (or (char= c #\A)
		      (char= c #\D)))
		(cdr (butlast chars))))))))

(defun cxr-symbol-to-cxr-list (s)
  (labels ((collect (l)
	     (if l
		 (list*
		  1
		  (if (char= (car l) #\A)
		      'A
		      'D)
		  (collect (cdr l))))))
    (collect
	(cdr ; chop off C
	 (butlast ; chop off R
	  (coerce
	   (symbol-name s)
	   'list))))))

(defmacro with-all-cxrs (&rest forms)
  `(labels
       (,@(mapcar
	   (lambda (s)
	     `(,s (l)
		  (cxr ,(cxr-symbol-to-cxr-list s)
		       l)))
	   (remove-duplicates
	    (remove-if-not
	     #'cxr-symbol-p
	     (flatten forms)))))
     ,@forms))

(defmacro! dlambda (&rest ds)
  `(lambda (&rest ,g!args)
     (case (car ,g!args)
       ,@(mapcar
	  (lambda (d)
	    `(,(if (eq t (car d))
		   t
		   (list (car d)))
	       (apply (lambda ,@(cdr d))
		      ,(if (eq t (car d))
			   g!args
			   `(cdr ,g!args)))))
	  ds))))

;; alambda Грэма
(defmacro alambda (parms &body body)
  `(labels ((self ,parms ,@body))
     #'self))

;; aif Грэма
(defmacro aif (test then &optional else)
  `(let ((it ,test))
     (if it ,then ,else)))

(defun |#`-reader| (stream sub-char numarg)
  (declare (ignore sub-char))
  (unless numarg (setq numarg 1))
  `(lambda ,(loop for i from 1 to numarg
	       collect (symb 'a i))
     ,(funcall
       (get-macro-character #\`) stream nil)))

(set-dispatch-macro-character
 #\# #\` #'|#`-reader|)

(defmacro alet% (letargs &rest body)
  `(let ((this) ,@letargs)
     (setq this ,@(last body))
     ,@(butlast body)
     this))

(defmacro alet (letargs &rest body)
  `(let ((this) ,@letargs)
     (setq this ,@(last body))
     ,@(butlast body)
     (lambda (&rest params)
       (apply this params))))

(defmacro alet-fsm (&rest states)
  `(macrolet ((state (s)
		`(setq this #',s)))
     (labels (,@states) #',(caar states))))

(defmacro! ichain-before (&rest body)
  `(let ((,g!indir-env this))
     (setq this
	   (lambda (&rest ,g!temp-args)
	     ,@body
	     (apply ,g!indir-env
		    ,g!temp-args)))))

(defmacro! ichain-after (&rest body)
  `(let ((,g!indir-env this))
     (setq this
	   (lambda (&rest ,g!temp-args)
	     (prog1
		 (apply ,g!indir-env
			,g!temp-args)
	       ,@body)))))

(defmacro! ichain-intercept% (&rest body)
  `(let ((,g!indir-env this))
     (setq this
	   (lambda (&rest ,g!temp-args)
	     (block intercept
	       (prog1
		   (apply ,g!indir-env
			  ,g!temp-args)
		 ,@body))))))

(defmacro! ichain-intercept (&rest body)
  `(let ((,g!indir-env this))
     (setq this
	   (lambda (&rest ,g!temp-args)
	     (block ,g!intercept
	       (macrolet ((intercept (v)
			    `(return-from
			      ,',g!intercept
			       ,v)))
		 (prog1
		     (apply ,g!indir-env
			    ,g!temp-args)
		   ,@body)))))))

(defmacro alet-hotpatch% (letargs &rest body)
  `(let ((this) ,@letargs)
     (setq this ,@(last body))
     ,@(butlast body)
     (lambda (&rest args)
       (if (eq (car args) ':hotpatch)
	   (setq this (cadr args))
	   (apply this args)))))

(defmacro alet-hotpatch (letargs &rest body)
  `(let ((this) ,@letargs)
     (setq this ,@(last body))
     ,@(butlast body)
     (dlambda
      (:hotpatch (closure)
		 (setq this closure))
      (t (&rest args)
	 (apply this args)))))

(defmacro! let-hotpatch (letargs &rest body)
  `(let ((,g!this) ,@letargs)
     (setq ,g!this ,@(last body))
     ,@(butlast body)
     (dlambda
      (:hotpatch (closure)
		 (setq ,g!this closure))
      (t (&rest args)
	 (apply ,g!this args)))))

(defmacro sublet (bindings% &rest body)
  (let ((bindings (let-binding-transform
		   bindings%)))
    (setq bindings
	  (mapcar
	   (lambda (x)
	     (cons (gensym (symbol-name (car x))) x))
	   bindings))
    `(let (,@(mapcar #'list
                     (mapcar #'car bindings)
                     (mapcar #'caddr bindings)))
       ,@(tree-leaves
	  body
	  #1=(member x bindings :key #'cadr)
	  (caar #1#)))))

(defmacro sublet* (bindings &rest body)
  `(sublet ,bindings
	   ,@(mapcar #'macroexpand-1 body)))

(defmacro pandoriclet (letargs &rest body)
  (let ((letargs (cons
		  '(this)
		  (let-binding-transform
		   letargs))))
    `(let (,@letargs)
       (setq this ,@(last body))
       ,@(butlast body)
       (dlambda
	(:pandoric-get (sym)
		       ,(pandoriclet-get letargs))
	(:pandoric-set (sym val)
		       ,(pandoriclet-set letargs))
	(t (&rest args)
	   (apply this args))))))

(declaim (inline get-pandoric))

(defun get-pandoric (box sym)
  (funcall box :pandoric-get sym))

(defsetf get-pandoric (box sym) (val)
  `(progn
     (funcall ,box :pandoric-set ,sym ,val)
     ,val))

(defmacro! with-pandoric (syms o!box &rest body)
  `(symbol-macrolet
       (,@(mapcar #`(,a1 (get-pandoric ,g!box ',a1))
		  syms))
     ,@body))

(defun pandoric-hotpatch (box new)
  (with-pandoric (this) box
		 (setq this new)))

(defmacro pandoric-recode (vars box new)
  `(with-pandoric (this ,@vars) ,box
		  (setq this ,new)))

(defmacro plambda (largs pargs &rest body)
  (let ((pargs (mapcar #'list pargs)))
    `(let (this self)
       (setq
	this (lambda ,largs ,@body)
	self (dlambda
	      (:pandoric-get (sym)
			     ,(pandoriclet-get pargs))
	      (:pandoric-set (sym val)
			     ,(pandoriclet-set pargs))
	      (t (&rest args)
		 (apply this args)))))))

(defun make-stats-counter
    (&key (count 0)
     (sum 0)
     (sum-of-squares 0))
  (plambda (n) (sum count sum-of-squares)
	   (incf sum-of-squares (expt n 2))
	   (incf sum n)
	   (incf count)))

(defmacro defpan (name args &rest body)
  `(defun ,name (self)
     ,(if args
	  `(with-pandoric ,args self
			  ,@body)
	  `(progn ,@body))))

(defpan stats-counter-mean (sum count)
  (/ sum count))

(defpan stats-counter-variance
    (sum-of-squares sum count)
  (if (< count 2)
      0
      (/ (- sum-of-squares
	    (* sum
	       (stats-counter-mean self)))
	 (- count 1))))

(defpan stats-counter-stddev ()
  (sqrt (stats-counter-variance self)))

(defun make-noisy-stats-counter
    (&key (count 0)
     (sum 0)
     (sum-of-squares 0))
  (plambda (n) (sum count sum-of-squares)
	   (incf sum-of-squares (expt n 2))
	   (incf sum n)
	   (incf count)
	   
	   (format t
		   "~&MEAN=~a~%VAR=~a~%STDDEV=~a~%"
		   (stats-counter-mean self)
		   (stats-counter-variance self)
		   (stats-counter-stddev self))))

(defvar pandoric-eval-tunnel)

(defmacro pandoric-eval (vars expr)
  `(let ((pandoric-eval-tunnel
	  (plambda () ,vars t)))
     (eval `(with-pandoric
		,',vars pandoric-eval-tunnel
		,,expr))))