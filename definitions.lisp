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
  (defun fact (x)
    (if (= x 0)
	1
	(* x (fact (- x 1)))))

  (defun choose (n r)
    (/ (fact n)
       (fact (- n r))
       (fact r)))

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
	 sym val))))

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

(set-dispatch-macro-character #\# #\f
   (lambda (stream sub-char numarg)
      (declare (ignore stream sub-char))
      (setq numarg (or numarg 3))
      (unless (<= numarg 3)
	(error "Bad value for #f: ~a" numarg))
      `(declare (optimize (speed ,numarg)
			  (safety ,(- 3 numarg))))))

(defmacro fast-progn (&rest body)
  `(locally '#f ,@body))

(defmacro safe-progn (&rest body)
  `(locally '#0f ,@body))

(defun fast-keywords-strip (args)
  (if args
    (cond
      ((eq (car args) '&key)
        (fast-keywords-strip (cdr args)))
      ((consp (car args))
        (cons (caar args)
	      #1=(fast-keywords-strip
		   (cdr args))))
      (t
        (cons (car args) #1#)))))

(defmacro! defun-with-fast-keywords
           (name args &rest body)
  `(progn
     (defun ,name ,args ,@body)
     (defun ,g!fast-fun
	    ,(fast-keywords-strip args)
            ,@body)
     (compile ',g!fast-fun)
     (define-compiler-macro ,name (&rest ,g!rest)
       (destructuring-bind ,args ,g!rest
	 (list ',g!fast-fun
		,@(fast-keywords-strip args))))))

(defun
  slow-keywords-test (a b &key (c 0) (d 0))
  (+ a b c d))

(compile 'slow-keywords-test)

(defun-with-fast-keywords
  fast-keywords-test (a b &key (c 0) (d 0))
  (+ a b c d))

(defun keywords-benchmark (n)
  (format t "Slow keys:~%")
  (time
    (loop for i from 1 to n do
      (slow-keywords-test 1 2 :d 3 :c n)))
  (format t "Fast keys:~%")
  (time
   (loop for i from 1 to n do
     (fast-keywords-test 1 2 :d 3 :c n))))

(compile 'keywords-benchmark)

(defun fformat (&rest all)
  (apply #'format all))

(compile 'fformat)

(define-compiler-macro fformat
                       (&whole form
			stream fmt &rest args)
  (if (constantp fmt)
    (if stream
      `(funcall (formatter ,fmt)
	 ,stream ,@args)
      (let ((g!stream (gensym "stream")))
	`(with-output-to-string (,g!stream)
	   (funcall (formatter ,fmt)
	     ,g!stream ,@args))))
    form))

(defun fformat-benchmark (n)
  (format t "Format:~%")
  (time
    (loop for i from 1 to n do
      ( format nil "Hello ~a ~a~%" 'world n)))
  (format t "Fformat:~%")
  (time
    (loop for i from 1 to n do
      (fformat nil "Hello ~a ~a~%" 'world n))))

(compile 'fformat-benchmark)

(defmacro dis (args &rest body)
  `(disassemble
     (compile nil
       (lambda ,(mapcar (lambda (a)
                          (if (consp a)
                            (cadr a)
                            a))
                        args)
         (declare
           ,@(mapcar
               #`(type ,(car a1) ,(cadr a1))
               (remove-if-not #'consp args)))
         ,@body))))

(defmacro! pointer-& (obj)
  `(lambda (&optional (,g!set ',g!temp))
     (if (eq ,g!set ',g!temp)
       ,obj
       (setf ,obj ,g!set))))

(defun pointer-* (addr)
  (funcall addr))

(defsetf pointer-* (addr) (val)
  `(funcall ,addr ,val))

(defsetf pointer-& (addr) (val)
  `(setf (pointer-* ,addr) ,val))

(defmacro! with-fast-stack
           ((sym &key (type 'fixnum) (size 1000)
                      (safe-zone 100))
            &rest body)
  `(let ((,g!index ,safe-zone)
         (,g!mem (make-array ,(+ size (* 2 safe-zone))
                             :element-type ',type)))
     (declare (type (simple-array ,type) ,g!mem)
              (type fixnum ,g!index))
     (macrolet
       ((,(symb 'fast-push- sym) (val)
            `(locally #f
               (setf (aref ,',g!mem ,',g!index) ,val)
               (incf ,',g!index)))
         (,(symb 'fast-pop- sym) ()
            `(locally #f
               (decf ,',g!index)
               (aref ,',g!mem ,',g!index)))
         (,(symb 'check-stack- sym) ()
            `(progn
               (if (<= ,',g!index ,,safe-zone)
                 (error "Stack underflow: ~a"
                        ',',sym))
               (if (<= ,,(- size safe-zone)
                       ,',g!index)
                 (error "Stack overflow: ~a"
                        ',',sym)))))
         ,@body)))

(declaim (inline make-tlist tlist-left
                 tlist-right tlist-empty-p))

(defun make-tlist () (cons nil nil))
(defun tlist-left (tl) (caar tl))
(defun tlist-right (tl) (cadr tl))
(defun tlist-empty-p (tl) (null (car tl)))

(declaim (inline tlist-add-left
                 tlist-add-right))

(defun tlist-add-left (tl it)
  (let ((x (cons it (car tl))))
    (if (tlist-empty-p tl)
      (setf (cdr tl) x))
    (setf (car tl) x)))

(defun tlist-add-right (tl it)
  (let ((x (cons it nil)))
    (if (tlist-empty-p tl)
      (setf (car tl) x)
      (setf (cddr tl) x))
    (setf (cdr tl) x)))

(declaim (inline tlist-rem-left))

(defun tlist-rem-left (tl)
  (if (tlist-empty-p tl)
    (error "Remove from empty tlist")
    (let ((x (car tl)))
      (setf (car tl) (cdar tl))
      (if (tlist-empty-p tl)
        (setf (cdr tl) nil)) ;; For gc
      (car x))))

(declaim (inline tlist-update))

(defun tlist-update (tl)
  (setf (cdr tl) (last (car tl))))

(defvar number-of-conses 0)

(declaim (inline counting-cons))

(defun counting-cons (a b)
  (incf number-of-conses)
  (cons a b))

(defmacro! with-conses-counted (&rest body)
  `(let ((,g!orig number-of-conses))
     ,@body
     (- number-of-conses ,g!orig)))

(defmacro counting-push (obj stack)
  `(setq ,stack (counting-cons ,obj ,stack)))

(defmacro with-cons-pool (&rest body)
  `(let ((cons-pool)
         (cons-pool-count 0)
         (cons-pool-limit 100))
     (declare (ignorable cons-pool
                         cons-pool-count
                         cons-pool-1imit))
     ,@body))

(defmacro! cons-pool-cons (o!car o!cdr)
  `(if (= cons-pool-count 0)
     (counting-cons ,g!car ,g!cdr)
     (let ((,g!cell cons-pool))
       (decf cons-pool-count)
       (setf cons-pool (cdr cons-pool))
       (setf (car ,g!cell) ,g!car
             (cdr ,g!cell) ,g!cdr)
       ,g!cell)))

(defmacro! cons-pool-free (o!cell)
  `(when (<= cons-pool-count
             (- cons-pool-limit 1))
     (incf cons-pool-count)
     (setf (car ,g!cell) nil)
     (push ,g!cell cons-pool)))

(defmacro make-cons-pool-stack ()
  `(let (stack)
     (dlambda
       (:push (elem)
         (setf stack
               (cons-pool-cons elem stack)))
       (:pop ()
         (if (null stack)
           (error "Tried to pop an empty stack"))
         (let ((cell stack)
               (elem (car stack)))
           (setf stack (cdr stack))
           (cons-pool-free cell)
           elem)))))

(with-cons-pool
  (defun make-shared-cons-pool-stack ()
     (make-cons-pool-stack)))

(defmacro with-dynamic-cons-pools (&rest body)
  `(locally (declare (special cons-pool
                              cons-pool-count
                              cons-pool-limit))
     ,@body))

(defmacro fill-cons-pool ()
  `(let (tp)
     (loop for i from cons-pool-count
                 to cons-pool-limit
           do (push
                (cons-pool-cons nil nil)
                tp))
     (loop while tp
           do (cons-pool-free (pop tp)))))

(defvar bad-3-sn
  '((0 1) (0 2) (1 2))) 

(defvar good-3-sn
  '((0 2) (0 1) (1 2))) 

(defvar tracing-interpret-sn nil)

(defun interpret-sn (data sn)
  (let ((step 0) (swaps 0))
    (dolist (i sn)
      (if tracing-interpret-sn
        (format t "Step ~a: ~a~%" step data))
      (if (> #1=(nth (car i) data)
             #2=(nth (cadr i) data))
        (progn
          (rotatef #1# #2#)
          (incf swaps)))
      (incf step))
    (values swaps data)))

(defun all-sn-perms (n)
  (let (perms curr)
    (funcall
      (alambda (left)
        (if left
          (loop for i from 0 to (1- (length left)) do
            (push (nth i left) curr)
            (self (append (subseq left 0 i)
                          (subseq left (1+ i))))
            (pop curr))
           (push curr perms)))
       (loop for i from 1 to n collect i))
     perms))

(defun average-swaps-calc (n sn)
  (/ (loop for i in (all-sn-perms n) sum
       (interpret-sn (copy-list i) sn))
     (fact n)))

(defun build-batcher-sn (n)
  (let* (network
         (tee (ceiling (log n 2)))
         (p (ash 1 (- tee 1))))
    (loop while (> p 0) do
      (let ((q (ash 1 (- tee 1)))
            (r 0)
            (d p))
        (loop while (> d 0) do
          (loop for i from 0 to (- n d 1) do
            (if (= (logand i p) r)
              (push (list i (+ i d))
                    network)))
          (setf d (- q p)
                q (ash q -1)
                r p)))
      (setf p (ash p -1)))
    (nreverse network)))

(defun prune-sn-for-median (elems network)
  (let ((mid (floor elems 2)))
    (nreverse
      (if (evenp elems)
        (prune-sn-for-median-aux
          (reverse network)
          (list (1- mid) mid))
        (prune-sn-for-median-aux
          (reverse network)
          (list mid))))))

(defun prune-sn-for-median-aux (network contam)
  (if network
    (if (intersection (car network) contam)
      (cons (car network)
            (prune-sn-for-median-aux
              (cdr network)
              (remove-duplicates
                 (append (car network) contam))))
      (prune-sn-for-median-aux
        (cdr network) contam)))) 

(defun prune-sn-for-median-calc (n)
  (loop for i from 2 to n collect
    (let* ((sn (build-batcher-sn i))
           (snp (prune-sn-for-median i sn)))
      (list i
            (length sn)
            (length snp)))))

(defvar paeth-9-median-sn
  '((0 3) (1 4) (2 5) (0 1) (0 2) (4 5) (3 5) (1 2)
    (3 4) (1 3) (1 6) (4 6) (2 6) (2 3) (4 7) (2 4)
    (3 7) (4 8) (3 8) (3 4)))

(defvar paeth-25-median-sn
  '((0 1) (3 4) (2 4) (2 3) (6 7) (5 7) (5 6) (9 10)
    (8 10) (8 9) (12 13) (11 13) (11 12) (15 16)
    (14 16) (14 15) (18 19) (17 19) (17 18) (21 22)
    (20 22) (20 21) (23 24) (2 5) (3 6) (0 6) (0 3)
    (4 7) (1 7) (1 4) (11 14) (8 14) (8 11) (12 15)
    (9 15) (9 12) (13 16) (10 16) (10 13) (20 23)
    (17 23) (17 20) (21 24) (18 24) (18 21) (19 22)
    (8 17) (9 18) (0 18) (0 9) (10 19) (1 19) (1 10)
    (11 20) (2 20) (2 11) (12 21) (3 21) (3 12)
    (13 22) (4 22) (4 13) (14 23) (5 23) (5 14)
    (15 24) (6 24) (6 15) (7 16) (7 19) (13 21)
    (15 23) (7 13) (7 15) (1 9) (3 11) (5 17) (11 17)
    (9 17) (4 10) (6 12) (7 14) (4 6) (4 7) (12 14)
    (10 14) (6 7) (10 12) (6 10) (6 17) (12 17)
    (7 17) (7 10) (12 18) (7 12) (10 18) (12 20)
    (10 20) (10 12)))

(defun sn-to-lambda-form% (sn)
  `(lambda (arr)
     #f
     (declare (type (simple-array fixnum) arr))
     ,@(mapcar
         #`(if (> #1=(aref arr ,(car a1))
                  #2=(aref arr ,(cadr a1)))
             (rotatef #1# #2#))
         sn)
     arr))

(defun sn-to-lambda-form (sn)
  `(lambda (arr)
     #f
     (declare (type (simple-array fixnum) arr))
     ,@(mapcar
         #`(let ((a #1=(aref arr ,(car a1)))
                 (b #2=(aref arr ,(cadr a1))))
             (if (> a b)
               (setf #1# b
                     #2# a)))
         sn)
     arr))

(defmacro! sortf (comparator &rest places)
  (if places
    `(tagbody
       ,@(mapcar
       #`(let ((,g!a #1=,(nth (car a1) places))
               (,g!b #2=,(nth (cadr a1) places)))
           (if (,comparator ,g!b ,g!a)
             (setf #1# ,g!b
                   #2# ,g!a)))
       (build-batcher-sn (length places))))))

(defmacro sort-benchmark-time ()
  `(progn
     (setq sorter (compile nil sorter))
     (let ((arr (make-array
                n :element-type 'fixnum)))
       (time
         (loop for i from 1 to iters do
           (loop for j from 0 to (1- n) do
             (setf (aref arr j) (random n)))
           (funcall sorter arr))))))

(defun do-sort-benchmark (n iters)
  (let ((rs (make-random-state *random-state*)))
    (format t "CL sort:~%")
    (let ((sorter
            '(lambda (arr)
                #f
                (declare (type (simple-array fixnum)
                               arr))
                (sort arr #'<))))
       (sort-benchmark-time))

    (setf *random-state* rs)
    (format t "sortf:~%")
    (let ((sorter
            `(lambda (arr)
               #f
               (declare (type (simple-array fixnum)
                              arr))
               (sortf <
                 ,@(loop for i from 0 to (1- n)
                         collect `(aref arr ,i)))
               arr)))
     (sort-benchmark-time))))

(compile 'do-sort-benchmark)

(defun medianf-get-best-sn (n)
  (case n
    ((0)  (error "Need more places for medianf"))
    ((9)  paeth-9-median-sn)
    ((25) paeth-25-median-sn)
    (t    (prune-sn-for-median n
            (build-batcher-sn n)))))

(defmacro! medianf (&rest places)
  `(progn
     ,@(mapcar
         #`(let ((,g!a #1=,(nth (car a1) places))
                 (,g!b #2=,(nth (cadr a1) places)))
             (if (< ,g!b ,g!a)
               (setf #1# ,g!b
                     #2# ,g!a)))
         (medianf-get-best-sn (length places)))
     ,(nth (floor (1- (length places)) 2) ; lower
           places)))
