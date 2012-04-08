;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;; algebraic-reasoning.lisp
;;;
;;; Defines a package for handling SparQ commands for reasoning about
;;; multivirate polynomial algebra

;; Change history (most recent first):
;; 2009-12-01 DW  unified report scheme for analyze-operation that acknowledges model-finding
;; 2009-10-19 DW  added satisfiability and polynomials command
;; 2008-05-16 DW  poly parsing is now done at calculi compile time, bug fix in analyze-operation (ho
;; 2008-05-13 DW  changed to infix notation in specification
;; 2008-05-09 DW  added intervals
;; 2007-05-04 DW  started this file

(defpackage :algebraic-reasoning
  (:use :common-lisp)
  (:nicknames :a-reasoning)
  (:export :process-command :a-model))

(in-package :algebraic-reasoning)

(defparameter *var-names-alist* '((:point (ax ay) (bx by) (cx cy))
				  (:2d-point (ax ay) (bx by) (cx cy))
				  (:1d-point (ax) (bx) (cx))
				  (:interval (a1 a2) (b1 b2) (c1 c2))
				  (:dipole (sax say eax eay) (sbx sby ebx eby) (scx scy ecx ecy))
				  (:oriented-point (ax ay adx ady) (bx by bdx bdy) (cx cy cdx cdy))))

;; Replaces named variables (e.g. sax, say) in a polynomial 'x', or any tree structure reresented
;; by lists accoring to the replacement scheme 'var-rpl'
(defun replace-vars (x var-rpl)
  (cond ((atom x) (if (symbolp x) (let ((rpl (assoc x var-rpl :test #'(lambda (s1 s2) (string= (symbol-name s1) (symbol-name s2))))))
				     (if rpl
					 (cdr rpl)
					 x)) ;; <- maybe raise a warning since there shouldn't be any symbols left
		      x))
	((listp x) (mapcar #'(lambda (y) (replace-vars y var-rpl)) x))))

;; Returns the polynomials for modeling 'relation' in 'calculus'
;; Slack variable may be introduced starting with the index slack-idx
;; Equations and index of next unsassigned slack variable ist returned
(defun a-modeling (calculus relation slack-idx)
  (let* ((relrep (calculi:calculus-relation-representation calculus))
	 (idx ())
	 (no-watch-slacks ())
	 (eqns ()))
    (ofunc:ofuncall (relations:relation-representation-mapper relrep)
		    #'(lambda (i)
			(push i idx))
		    relation)
    (when (or (null idx) (cdr idx))
      (sparq:signal-error "Error in algebraic scenario modeling: only base relations are allowed"))
    (flet ((parse-poly (p)
	     (cond ((listp p) p)
		   ((numberp p) (list (list p nil)))
		   (t (sparq:signal-error "Cannot parse polynomial in algebraic spec: ~a" p)))))      
      (dolist (eq (aref (calculi::calculus-algebraic-spec calculus) (car idx)))
	(let ((op (first eq))
	      (side-l (parse-poly (second eq)))
	      (side-r (parse-poly (third eq))))
	  ;(format t "~&--> eq=~w   ==>  ~a '~a' ~a~%" eq side-l op side-r)
	  
	  (cond ((eq op '=) (push (append side-l (mapcar #'(lambda (term)
							     (cons (- (first term)) (rest term)))
							 side-r))
				  eqns))
		((eq op '<) (push (append side-l
					  (list (list 1 (list (list slack-idx 2))))
					  (mapcar #'(lambda (term)
						      (cons (- (first term)) (rest term)))
						  side-r))
				  eqns)
		            (incf slack-idx))
		((eq op '>) (push (append side-l
					  (list (list -1 (list (list slack-idx 2))))
					  (mapcar #'(lambda (term)
						      (cons (- (first term)) (rest term)))
						  side-r))
				  eqns)
		             (incf slack-idx))
		((eq op '>=) (push slack-idx no-watch-slacks)
		             (push (append side-l
					   (list (list -1 (list (list slack-idx 2))))
					   (mapcar #'(lambda (term)
						       (cons (- (first term)) (rest term)))
						   side-r))
				   eqns)
		             (incf slack-idx))

		 ((eq op '<=) (push slack-idx no-watch-slacks)
		              (push (append side-l
					    (list (list 1 (list (list slack-idx 2))))
					    (mapcar #'(lambda (term)
							(cons (- (first term)) (rest term)))
						    side-r))
				    eqns)
		               (incf slack-idx))
	  
		 (t (sparq:signal-error "Cannot process algebraic spec, relation <, >, = required but '~a' found" op))))))    
    (values (mapcar #'(lambda (eq) ; filter out "+ 0" terms
			(remove '(0 ()) eq :test #'equal))
		    eqns)
	    slack-idx
	    no-watch-slacks)))


;; Returns a list of polynomial equation describing scenario
;; as a 2nd return value, the list of slack variables is returned
(defun a-scenario (stream calculus scenario)
  (multiple-value-bind (objects constraints) (constraint-reasoning::parse-constraint-network calculus scenario :allow-multiple-definitions? t)
    (setq objects (sort objects #'string< :key #'symbol-name))
    (let* ((entity-var-names (cdr (assoc (calculi:calculus-basis-entity calculus) *var-names-alist*)))
	   (arity (cdr (assoc (calculi:calculus-arity calculus) '((:binary . 2) (:ternary . 3)))))
	   (var-names (butlast entity-var-names (- 3 arity)))
	   (vars-per-obj (length (first entity-var-names))))
      (unless var-names
	(sparq:signal-error "Don't know how to handle basis entity '~a'" (calculi:calculus-basis-entity calculus)))
      ;; Print out variable assignments
      (when sparq:*debug*
	(format stream "~&;;~%;; Variable assignment~%;;")
	(let ((count 1))
	  (dolist (o objects)
	    (format stream "~%;;~a := (" o )
	    (dolist (var (first entity-var-names))
	      (format stream "~a_~a " o var))
	    (format stream ") <- (")
	    (dotimes (i vars-per-obj)
	      (format stream "x[~a] " count) 
	      (incf count))
	    (format stream ")")))
	(format stream "~%;;~%;; Constraint modeling~%;;"))
      (let* ((eqns ()) ; Equations modeling the scenario
	     (slack-idx0 (* 10 (+ 1 (ceiling (* (length objects) vars-per-obj) 10)))) ; lowest variable index used for slack vars
	     (slack-idx slack-idx0)) ; 'pointer' to current slack index 
	;; construct polynomial equations to model the constraints
	(dolist (c constraints)
	  (let* ((objs (append (if (listp (constraint-reasoning::constraint-object-1 c))  ; list of objects involved in constraint
				   (constraint-reasoning::constraint-object-1 c)
				   (list (constraint-reasoning::constraint-object-1 c)))
			       (list (constraint-reasoning::constraint-object-2 c))))
		 (var-rpl (apply #'append (mapcar #'(lambda (obj names) ; variables (i.e. indices) used to represent the vars as assoc list
						      (let ((idx (+ 1 (* vars-per-obj (position obj objects)))))
							(mapcar #'(lambda (sym)
								    (prog1 
									(cons sym idx)
								      (incf idx)))
								names)))
						  objs var-names))))
	    (multiple-value-bind (rel-eqns new-idx) (a-modeling calculus (constraint-reasoning::constraint-relation c) slack-idx)
	      (setq slack-idx new-idx
		    eqns (nconc (mapcar #'(lambda (eq)
					    (replace-vars eq var-rpl))
					rel-eqns)
				eqns)))))
	(setq eqns (mapcar #'poly::make-poly eqns)) ; sort polys according to term ordering
	(when sparq:*debug*
	  (let ((cnt 0))
	    (dolist (eq eqns)
	      (format stream "~%;;(~2a:) " (incf cnt))
	      (poly:print-poly eq stream))))
	(values eqns 
		(loop for i from slack-idx0 to (- slack-idx 1) collect i) 
		(loop for x in objects 
		      for y upfrom 1 by vars-per-obj 
		   collect (cons x (loop for i from y below (+ y vars-per-obj) collect i))))))))


;;; Tests a given scenario or consistency by testing the Groebner basis 
;;; for satisfiability
(defun a-consistency (stream calculus scenario &key silent?)
  (sparq:with-timing stream
    (multiple-value-bind (eqns slack-vars) (a-scenario stream calculus scenario)
      (let ((ib (cdr (assoc (calculi:calculus-basis-entity calculus) '((:1d-point . ((1 . 0)))
								       (:2d-point . ((1 . 0) (2 . 0) (3 . 0)))
								       (:point . ((1 . 0) (2 . 0)))
								       (:interval . ((1 . 0)))
								       (:dipole . ((1 . 0) (2 . 0) (3 . 0) (4 . 1)))
								       (:oriented-point . ((1 . 0) (2 . 0) (3 . 1) (4 . 0))))))))
	(sparq:report-time "polynomial modeling")
	(let ((result (poly:test-emptyness stream eqns slack-vars :initial-bindings ib)))
	  (unless silent?
	    (cond	((eq result :?) (format stream "~&CANNOT DECIDE.~%"))
			((null result)  (format stream "~&IS SATISFIABLE.~%"))
			(result         (format stream "~&NOT SATISFIABLE.~%"))))
	  result)))))

(defun eval-poly (poly var-rpl)
  (reduce #'(lambda (val term)
	      ;(format t "~% val= ~a, term=~a, var-rpl=~a" val term var-rpl)
	      (+ val (reduce #'(lambda (val var)
				 ;(format t "~& val=~a, var=~a" val var)
				 (let ((v  (cdr (assoc (first var) var-rpl :test #'(lambda (s1 s2) (string= (symbol-name s1) (symbol-name s2))))))
				       (exp (second var)))
				   ;(print v)
				   (unless (numberp v)
				     (sparq:signal-error "Cannot bind variable '~a' to object's position!" (first var)))
				   ;(format t "~% val=~a --> ~a" val (* val (expt v exp)))
				   (* val (expt v exp))))
			     (second term)
			     :initial-value (first term))))
	  poly
	  :initial-value 0))

;; determines the relation that holds given the variable bindings b
(defun qualify-obj (calculus b)
  (let* ((relrep (calculi:calculus-relation-representation calculus))
	 (br (relations:relation-representation-br-encodings relrep))
	 (n (relations:relation-representation-num-base-relations relrep))
	 (rel (relations:relation-representation-empty-relation relrep))
	 (aspec (calculi:calculus-algebraic-spec calculus)))
    ;; iterate over all base relations
    (dotimes (i n)
      (when (every #'(lambda (s)
		       (let ((op (first s))
			     (val-l (eval-poly (second s) b))
			     (val-r (eval-poly (third s) b)))
			 (case op
			   (< (< val-l val-r))
			   (= (= val-l val-r))
			   (> (> val-l val-r))
			   (>= (>= val-l val-r))
			   (<= (<= val-l val-r))
			   (/= (/= val-l val-r))
			   (otherwise (sparq:signal-error "Cannot handle operator '~a' in algebraic specicfication (only <, =, > are allowed)" op)))))
		   (aref aspec i))
	(setq rel (calculi:unite calculus rel (svref br i)))))
    rel))  

;; creates binding like ((sax . 7) (eax . 1) ...) from a object spec (e.g., (A 1 2 4 2)) and
;; a var list (e.g., (sax eax say eay))
(declaim (inline obj-var-bindings))
(defun obj-var-bindings (ospec varlist)
  (mapcar #'cons varlist (cdr ospec)))


;; Qualification based on algebraic spec
;; 4 cases distinguished: binary/ternary calulus, option first2all/all
;; Constructs variable bindings for the objects and calls qualify-obj which
;; evaluates the polynomial expressions and returns the right relations
(defun qualify (stream calculus args)
  (let ((option (pop args))
	(b (calculi:calculus-basis-entity calculus)))
    (setq args (first args))
    (mapc #'(lambda (x)
	      (qualifier:parse-entity b x))
	  args) ; Error checking
    (let* ((entity-var-names (cdr (assoc b *var-names-alist*)))
	   (arity (cdr (assoc (calculi:calculus-arity calculus) '((:binary . 2) (:ternary . 3)))))
	   (var-names (butlast entity-var-names (- 3 arity))))
      (unless var-names
	(sparq:signal-error "Don't know how to handle basis entity '~a'" (calculi:calculus-basis-entity calculus)))
      (flet ((decode-rel (r)
	       (ofunc:ofuncall (relations:relation-representation-decoder (calculi:calculus-relation-representation calculus)) (calculi:calculus-relation-representation calculus) r)))
	(if (eq arity 2)
	    ;; qualify a binary calculus
	    (cond ((eq option 'cl-user::first2all)
		   (let ((o1-bindings (obj-var-bindings (first args) (first entity-var-names)))
			 (o1 (caar args)))
		     (write-char #\( stream)
		     (dolist (o2 (rest args))
		       (let ((o2-bindings (obj-var-bindings o2 (second entity-var-names))))
			 (format stream "(~a ~a ~a) " o1 (decode-rel (qualify-obj calculus (append o1-bindings o2-bindings))) (car o2))))
		     (write-char #\) stream)))
		  ((eq option 'cl-user::all)
		   (write-char #\( stream)
		   (do ((o1s args (cdr o1s)))
		       ((null o1s))
		     (let* ((o1-bindings (obj-var-bindings (first o1s) (first entity-var-names)))
			    (o1 (caar o1s)))
		       (dolist (o2 (rest o1s))
			 (let ((o2-bindings (obj-var-bindings o2 (second entity-var-names))))
			   (format stream "(~a ~a ~a) " o1 (decode-rel (qualify-obj calculus (append o1-bindings o2-bindings))) (car o2))))))
		   (write-char #\) stream))
		  (t (sparq:signal-error "Option '~a' to algebraic qualifier not supported!" option)))
	    
	    (cond ((eq option 'cl-user::first2all)
		   (let ((o1-bindings (obj-var-bindings (first args) (first entity-var-names)))
			 (o1 (caar args))
			 (o2-bindings (obj-var-bindings (second args) (second entity-var-names)))
			 (o2 (car (second args))))
		     (write-char #\( stream)
		     (dolist (o3 (cddr args))
		       (let ((o3-bindings (obj-var-bindings o3 (third entity-var-names))))
			 (format stream "(~a ~a ~a ~a) " o1 o2 (decode-rel (qualify-obj calculus (append o1-bindings o2-bindings o3-bindings))) (car o3))))
		     (write-char #\) stream)))
		  ((eq option 'cl-user::all)
		   (write-char #\( stream)
		   (do ((o1s args (cdr o1s)))
		       ((null o1s))
		     (let* ((o1-bindings (obj-var-bindings (first o1s) (first entity-var-names)))
			    (o1 (caar o1s)))
		       (do ((o2s (cdr o1s) (cdr o2s)))
			   ((null o2s))
			 (let* ((o2-bindings (obj-var-bindings (first o2s) (second entity-var-names)))
				(o2 (caar o2s)))
			   (dolist (o3 (rest o2s))
			     (let ((o3-bindings (obj-var-bindings o3 (third entity-var-names))))
			     (format stream "(~a ~a ~a ~a) " o1 o2 (decode-rel (qualify-obj calculus (append o1-bindings o2-bindings o3-bindings))) (car o3))))))))
		   (write-char #\) stream))
		  (t (sparq:signal-error "Option '~a' to algebraic qualifier not supported!" option)))

	    )))))

;;;
;;; generate composition table entries by random network instantiation
;;;
(defun generate-binary-composition-scenarios (calculus time/msec)
  (let* ((b (calculi:calculus-basis-entity calculus))
	 (entity-var-names (cdr (assoc b *var-names-alist*)))
	 (arity (cdr (assoc (calculi:calculus-arity calculus) '((:binary . 2) (:ternary . 3)))))
	 (relrep (calculi:calculus-relation-representation calculus))
	 (comptable (make-array (list (relations:relation-representation-num-base-relations relrep)
				      (relations:relation-representation-num-base-relations relrep))
				:initial-element (relations:relation-representation-empty-relation relrep)))
	 (endtime (+ (get-internal-real-time) time/msec)))
    (labels ((decode-rel (r)
	       (ofunc:ofuncall (relations:relation-representation-decoder relrep) relrep r))
	     (rel-idx (r)
	       (ofunc:ofuncall (relations:relation-representation-mapper relrep)
			       #'(lambda (i)
				   (return-from rel-idx i))
			       r))
	     (random-coordinate ()
	       (random 19))
	     (register-bin-rel (a-coor b-coor c-coor)
	       (let ((r-ab (let ((a-bindings (mapcar #'cons (first entity-var-names) a-coor))
				 (b-bindings (mapcar #'cons (second entity-var-names) b-coor)))
			     (qualify-obj calculus (nconc a-bindings b-bindings))))
		     (r-bc (let ((b-bindings (mapcar #'cons (first entity-var-names) b-coor))
				 (c-bindings (mapcar #'cons (second entity-var-names) c-coor)))
			     (qualify-obj calculus (nconc b-bindings c-bindings))))
		     (r-ac (let ((a-bindings (mapcar #'cons (first entity-var-names) a-coor))
				 (c-bindings (mapcar #'cons (second entity-var-names) c-coor)))
			     (qualify-obj calculus (nconc a-bindings c-bindings)))))
		 (let ((r-ab-idx (rel-idx r-ab))
		       (r-bc-idx (rel-idx r-bc)))
		   (when (and r-ab-idx r-bc-idx)
		     (setf (aref comptable r-ab-idx r-bc-idx) (ofunc:ofuncall (relations:relation-representation-unite relrep)
									      (aref comptable r-ab-idx r-bc-idx) 
									      r-ac))))))
	     (register-rel (a-coor b-coor c-coor d-coor)
	       (let ((r-abc (let ((a-bindings (mapcar #'cons (first entity-var-names) a-coor))
				  (b-bindings (mapcar #'cons (second entity-var-names) b-coor))
				  (c-bindings (mapcar #'cons (third entity-var-names) c-coor)))
			      (qualify-obj calculus (nconc a-bindings b-bindings c-bindings))))
		     (r-bcd (let ((b-bindings (mapcar #'cons (first entity-var-names) b-coor))
				  (c-bindings (mapcar #'cons (second entity-var-names) c-coor))
				  (d-bindings (mapcar #'cons (third entity-var-names) d-coor)))
			      (qualify-obj calculus (nconc b-bindings c-bindings d-bindings))))
		     (r-abd (let ((a-bindings (mapcar #'cons (first entity-var-names) a-coor))
				  (b-bindings (mapcar #'cons (second entity-var-names) b-coor))
				  (d-bindings (mapcar #'cons (third entity-var-names) d-coor)))
			      (qualify-obj calculus (nconc a-bindings b-bindings d-bindings)))))
		 (let ((r-abc-idx (rel-idx r-abc))
		       (r-bcd-idx (rel-idx r-bcd)))
		   (when (and r-abc-idx r-bcd-idx)
		     (setf (aref comptable r-abc-idx r-bcd-idx) (ofunc:ofuncall (relations:relation-representation-unite relrep)
										(aref comptable r-abc-idx r-bcd-idx) 
										r-abd)))))))
	    ;; get all easy case by exhaustive search
	    (labels ((step-coordinate (c)
		       (if c
			 (let ((x (incf (first c))))
			   (if (= x 4)
			       (progn
				 (setf (first c) 0)
				 (step-coordinate (cdr c)))
			       nil))
			 t)))

	      (if (eq arity 2)
	  ;; handle a binary calculus
	  (progn
	    (let ((a-coor (mapcar (constantly 1) (first entity-var-names)))
		  (b-coor (mapcar (constantly 0) (first entity-var-names)))
		  (c-coor (mapcar (constantly 0) (first entity-var-names)))
		  (done? nil))
	      (loop until done? do
		   (register-bin-rel a-coor b-coor c-coor)
		   (when (step-coordinate c-coor)
		     (when (step-coordinate b-coor)
		       (setq done? t)))))
	    (loop while (< (get-internal-real-time) endtime) do
		 (dotimes (i 100) ; just to not waste time checking for timeout after every test
		   (let ((a-coor (mapcar (constantly 0) (first entity-var-names)))
			 (b-coor (mapcar #'(lambda (x) (declare (ignore x)) (random-coordinate)) (first entity-var-names)))
			 (c-coor (mapcar #'(lambda (x) (declare (ignore x)) (random-coordinate)) (first entity-var-names))))
		     (register-bin-rel a-coor b-coor c-coor))))
	    comptable)
	  ;; handle ternary calculus (with binary composition)
	  (progn 	    
	      (let ((a-coor (mapcar (constantly 1) (first entity-var-names)))
		    (b-coor (mapcar (constantly 0) (first entity-var-names)))
		    (c-coor (mapcar (constantly 0) (first entity-var-names)))
		    (d-coor (mapcar (constantly 0) (first entity-var-names)))
		    (done? nil))
		(loop until done? do
		     (register-rel a-coor b-coor c-coor d-coor)
		     (when (step-coordinate d-coor)
		       (when (step-coordinate c-coor)
			 (when (step-coordinate b-coor)
			   (setq done? t))))))

	    (loop while (< (get-internal-real-time) endtime) do
		 (dotimes (i 100) ; just to not waste time checking for timeout after every test
		   (let ((a-coor (mapcar (constantly 0) (first entity-var-names)))
			 (b-coor (mapcar #'(lambda (x) (declare (ignore x)) (random-coordinate)) (first entity-var-names)))
			 (c-coor (mapcar #'(lambda (x) (declare (ignore x)) (random-coordinate)) (first entity-var-names)))
			 (d-coor (mapcar #'(lambda (x) (declare (ignore x)) (random-coordinate)) (first entity-var-names))))
		     (register-rel a-coor b-coor c-coor d-coor))))))
	  comptable))))
	

;;;
;;; ANALYZE-OPERATION
;;;	     

(defun report-analysis-result (stream calculus table-rel negative-rels positive-rels)
  (let* ((extra-comp  (calculi:intersect calculus table-rel negative-rels)) ; rels in operation table def but not possible
	 (extra-acomp (calculi:minus calculus positive-rels table-rel)) ; rels missing in the operation table
	 (missed (calculi:compl calculus (calculi:unite calculus positive-rels negative-rels)))
	 (missed-unsatisfiable (calculi:minus calculus (calculi:compl calculus table-rel) negative-rels))
	 (missed-models (calculi:minus calculus table-rel positive-rels))
	 (ok? t)
	 (rel-rep (calculi:calculus-relation-representation calculus))
	 (decoder (relations:relation-representation-decoder rel-rep))
	 (empty-rel? (relations:relation-representation-empty-relation? rel-rep))
	 (xterm-printing? (let ((term (sb-ext:posix-getenv "TERM")))
			   (and term
				(string= "xterm" term :end2 5)))))

    (when (not (ofunc:ofuncall empty-rel? extra-acomp))
      (setq ok? nil)
      (if xterm-printing?
	  (format stream "~a[1mALSO INCLUDES:~a[0m ~a " #\ESC #\ESC (ofunc:ofuncall decoder rel-rep extra-acomp))
	  (format stream "ALSO INCLUDES: ~a " (ofunc:ofuncall decoder rel-rep extra-acomp))))
    (when (not (ofunc:ofuncall empty-rel? extra-comp))
      (setq ok? nil)
      (if xterm-printing?
	  (format stream "~a[1mCANNOT INCLUDE  :~a[0m ~a " #\ESC #\ESC (ofunc:ofuncall decoder rel-rep extra-comp))
	  (format stream "CANNOT INCLUDE  : ~a " (ofunc:ofuncall decoder rel-rep extra-comp))))
    (when (not (ofunc:ofuncall empty-rel? missed-unsatisfiable))
      (setq ok? nil)
      (format stream "could not prove non-membership of : ~a " (ofunc:ofuncall decoder rel-rep missed-unsatisfiable)))
    (when (not (ofunc:ofuncall empty-rel? missed-models))
      (setq ok? nil)
      (format stream "could not prove membership of : ~a" (ofunc:ofuncall decoder rel-rep missed-models)))
    (when ok?
      (if xterm-printing?
	  (format stream "~a[1mVerified~a[0m" #\ESC #\ESC)
	  (format stream "Verified")))
    
    ;; return # of relation combinations not covered by the proofs
    (let ((misses (relations:relation-representation-num-base-relations rel-rep)))
      (ofunc:ofuncall (relations:relation-representation-mapper rel-rep) 
		      #'(lambda (idx) (declare (ignore idx)) (decf misses))
		      (calculi:unite calculus negative-rels positive-rels))
      misses)))


(defun analyze-ternary-composition (stream calculus)
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (u (relations:relation-representation-universal-relation rel-rep))
	 (e (relations:relation-representation-empty-relation rel-rep))
	 (mapper (relations:relation-representation-mapper rel-rep))
	 (empty-rel? (relations:relation-representation-empty-relation? rel-rep))
	 (decoder (relations:relation-representation-decoder rel-rep))
	 (rel-names (relations:relation-representation-base-relations rel-rep))
	 (n (relations:relation-representation-num-base-relations rel-rep))
	 (rels (relations:relation-representation-br-encodings rel-rep)))
    (format stream "~&progress~A r1      r2      r3     analysis" (if (< 8 n)
							      (coerce (make-list (- n 8) :initial-element #\.) 'string)
							      ""))
    (ofunc:ofuncall mapper #'(lambda (idx-1)
			       (let* ((r1 (svref rels idx-1))
				      (r1-name (svref rel-names idx-1)))
				 (ofunc:ofuncall mapper #'(lambda (idx-2)
							    (let ((r2 (svref rels idx-2))
								  (r2-name (svref rel-names idx-2)))
							      (ofunc:ofuncall mapper #'(lambda (idx-3)
											 (format stream "~%")
											 (let* ((r3 (svref rels idx-3))
												(r3-name (svref rel-names idx-3))
												(oks e)
												(noks e))
											   (ofunc:ofuncall mapper #'(lambda (idx-4)
														      (format stream ".")
														      (finish-output stream)
														      (let* ((r4 (svref rels idx-4))
															     (r4-name (svref rel-names idx-4))
															     (res (a-consistency stream calculus (list (list (list 'a 'b r1-name 'f)
																					     (list 'a 'f r2-name 'c)
																					     (list 'f 'b r3-name 'c)
																					     (list 'a 'b r4-name 'c)))
																		 :silent? t)))
															(if (eq res t)
															    (setq noks (calculi:unite calculus noks r4))
															    (if (eq res nil)
																(setq oks (calculi:unite calculus oks r4))))))
													   u)
											   ;; Evaluation
											   (format stream " ~8A~8A~8A " r1-name r2-name r3-name)
											   (report-analysis-result stream calculus (calculi:ternary-composition calculus r1 r2 r3) noks oks)))
									      u)))
						 u)))
		    u)))

;; 
;; Analyze the binary composition operation for either binary or ternary calculi
;;
(defun analyze-composition (stream calculus)
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (u (relations:relation-representation-universal-relation rel-rep))
	 (e (relations:relation-representation-empty-relation rel-rep))
	 (mapper (relations:relation-representation-mapper rel-rep))
	 (empty-rel? (relations:relation-representation-empty-relation? rel-rep))
	 (decoder (relations:relation-representation-decoder rel-rep))
	 (rel-names (relations:relation-representation-base-relations rel-rep))
	 (n (relations:relation-representation-num-base-relations rel-rep))
	 (rels (relations:relation-representation-br-encodings rel-rep))
	 (models (if (< n 30)
		     (progn
		       (format stream "~&preparing cache...")
		       (finish-output stream)
		       (generate-binary-composition-scenarios calculus 4000))))
	 (misses 0)
	 (filler (coerce (make-list (max 0 (- 8 n)) :initial-element #\Space) 'string)))

    (format stream "~&progress~A r1      r2     analysis~%~A" 
	    (coerce (make-list (max 0 (- n 8)) :initial-element #\.) 'string)
	    (coerce (make-list (+ 32 (max 0 (- n 8))) :initial-element #\-) 'string))
    (ofunc:ofuncall mapper #'(lambda (idx-1)
			       (let* ((r1 (svref rels idx-1))
				      (r1-name (svref rel-names idx-1)))
				 (ofunc:ofuncall mapper #'(lambda (idx-2)
							    (format stream "~%")
							    (let* ((r2 (svref rels idx-2))
								   (r2-name (svref rel-names idx-2))
								   ;; rels acceptable as composition result according to algebraic reasoning
								   (oks (if models
									    (aref models idx-1 idx-2)
									    e))
								   (neg e))
							      
							      (ofunc:ofuncall mapper #'(lambda (idx-3)
											 (format stream ".")
											 ;;(format stream "(~a ~a ~a)" r1-name r2-name (svref rel-names idx-3))
											 (finish-output stream)
											 (when (or t (ofunc:ofuncall empty-rel? (calculi:intersect calculus (svref rels idx-3) oks)))
											   (let* ((r3 (svref rels idx-3))
												  (r3-name (svref rel-names idx-3))
					;(now (get-internal-real-time))
												  (res (a-consistency stream calculus (if (eq :ternary (calculi:calculus-arity calculus))
																	  (list (list (list 'a 'b r1-name 'c)
																		      (list 'b 'c r2-name 'd)
																		      (list 'a 'b r3-name 'd)))
																	  (list (list (list 'a r1-name 'b)
																		      (list 'b r2-name 'c)
																		      (list 'a r3-name 'c))))
														      :silent? t)))
					;(format t "~%TIME ~a~%" (- (get-internal-real-time) now))
											     
					;(when (= 0 (decf testloop))
					; (return-from analyze-composition))
											     (if (eq res t)
												 (setq neg (calculi:unite calculus neg r3))
												 (if (eq res nil)
												     (setq oks (calculi:unite calculus oks r3)))))))
									      u)
							      ;; evaluation
							      (format stream " ~8A~8A~A" r1-name r2-name filler)
							      (incf misses (report-analysis-result stream calculus (calculi:composition calculus r1 r2) neg oks))))
						 u)))
		    u)
    (let ((total (expt n 3)))
      (format stream "~&Done. ~,2f% of the configurations (~d out of ~d) could not be verified/falsified." (/ (* 100.0 misses) total) misses total))))
  
  ;; analyzes 'operation' (e.g. calculi:shortcut, ...); csp-pattern is a csp network definition missing the relations
;; for example, for testing binary inverse supply the network '((a b) (b a)), for ternary homing '((a b c) (b c a))
(defun analyze-unary-operation (stream calculus operation csp-pattern)
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (u (relations:relation-representation-universal-relation rel-rep))
	 (e (relations:relation-representation-empty-relation rel-rep))
	 (mapper (relations:relation-representation-mapper rel-rep))
	 (empty-rel? (relations:relation-representation-empty-relation? rel-rep))
	 (decoder (relations:relation-representation-decoder rel-rep))
	 (rel-names (relations:relation-representation-base-relations rel-rep))
	 (n (relations:relation-representation-num-base-relations rel-rep))
	 (rels (relations:relation-representation-br-encodings rel-rep))
	 (filler (coerce (make-list (max 0 (- 8 n)) :initial-element #\Space) 'string)))
    (format stream "~&progress~A r        analysis~%---------~A-"
	    (coerce (make-list (max 0 (- n 8)) :initial-element #\.) 'string)
	    (coerce (make-list (+ 17 (max 0 (- n 8))) :initial-element #\-) 'string))
    (ofunc:ofuncall mapper #'(lambda (idx-1)
			       (format stream "~%")
			       (let* ((r1 (svref rels idx-1))
				      (r1-name (svref rel-names idx-1))
				      (oks e)   ; rels acceptable as composition result according to algebraic reasoning
				      (noks e)) ; rels not acceptable...

				 (ofunc:ofuncall mapper #'(lambda (idx-2)
							    (format stream ".")
							    (finish-output stream)
							    (let* ((r2 (svref rels idx-2))
								   (r2-name (svref rel-names idx-2))
								   (res (a-consistency stream calculus (list (mapcar #'(lambda (pattern r)
															 (append (butlast pattern) (cons r (last pattern))))
														     csp-pattern
														     (list r1-name r2-name)))
										       :silent? t)))
							      (if (eq res t)
								  (setq noks (calculi:unite calculus noks r2))
								  (if (eq res nil)
								      (setq oks (calculi:unite calculus oks r2))))))
						 u)
				 ;; Evaluate results
				 (format stream " ~A~8A " filler r1-name)
				 (report-analysis-result stream calculus (funcall operation calculus r1) noks oks)))
		    u)))

;; using algebraic reasoning to verify operation tables of some calculus
(defun analyze-operation (stream calculus args)
  (let ((operation (pop args)))
    (cond ((eq operation 'cl-user::composition) (analyze-composition stream calculus))

	  ((eq operation 'cl-user::shortcut) (if (eq (calculi:calculus-arity calculus) :ternary)
						 (analyze-unary-operation stream calculus #'calculi:shortcut '((a b c) (a c b)))
						 (sparq:signal-error "shortcut not defined for binary calculus ~A!" (calculi:calculus-name calculus))))

	  ((eq operation 'cl-user::homing) (if (eq (calculi:calculus-arity calculus) :ternary)
					       (analyze-unary-operation stream calculus #'calculi:homing '((a b c) (b c a)))
					       (sparq:signal-error "homing not defined for binary calculus ~A!" (calculi:calculus-name calculus))))

	  ((eq operation 'cl-user::inverse) (if (eq (calculi:calculus-arity calculus) :ternary)
						(analyze-unary-operation stream calculus #'calculi:inverse '((a b c) (b a c)))
						(sparq:signal-error "inverse not defined for binary calculus ~A!" (calculi:calculus-name calculus))))

	  ((eq operation 'cl-user::converse) (if (eq (calculi:calculus-arity calculus) :binary)
					       (analyze-unary-operation stream calculus #'calculi:converse '((a b) (b a)))
					       (sparq:signal-error "homing not defined for ternary calculus ~A!" (calculi:calculus-name calculus))))

	  ((eq operation 'cl-user::ternary-composition) (if (calculi:calculus-n-ary-composition calculus)
							    (analyze-ternary-composition stream calculus)
							    (sparq:signal-error "ternary composition not defined for calculus ~A!" (calculi:calculus-name calculus))))

	  (t (sparq:signal-error "Sorry, operation ~a cannot be verified" operation)))))

(defun a-model (stream calculus scenario)
  (setq *random-state* (make-random-state t))
  (format stream "~&;; NOTE: using numerical solver")
  (multiple-value-bind (eqns slacks obj-bindings) (a-scenario stream calculus scenario)
    ;; add extra equations to make the slack var of value 10
    
    (setq eqns (nconc (mapcar #'(lambda (s)
				  (poly:make-poly (list (list -1 ()) (list 1 (list (list s 2))))))
			      slacks)
		      eqns))
    
    (when sparq:*debug*
      (format stream "~&;; Polynomials:")
      (poly::print-poly-list eqns stream))
    (let* ((pre-bind '((1 . 0)))
	   (model-eqn (reduce #'(lambda (poly p)
				  (poly:add poly (poly:multiply p p)))
			      (poly::apply-bindings pre-bind eqns)
			      :initial-value ()))
	   (all-vars (poly-model:equation-variables model-eqn))
	   (model-deriv (poly-model:derivative model-eqn all-vars))
	   (model-found? nil)
	   obj-model
	   result)
      ;; try to find model:
      (do ((initial-state (mapcar #'(lambda (x)
				      (cons x (- (random 100) 50)))
				  all-vars)
			  (mapcar #'(lambda (x)
				      (cons x (- (random 100) 50)))
				  all-vars))
	   (tries 0 (+ tries 1)))
	  ((or (= tries 10)
	       model-found?))
	;;(print model-eqn)
	;;(print all-vars)
	(multiple-value-bind (model residual) (poly-model:compute-model stream model-eqn model-deriv all-vars initial-state)
	  (declare (ignore residual))
	  (let ((ext-model (append pre-bind model)))
	    (setq obj-model (mapcar #'(lambda (obj-binding)
					(cons (first obj-binding) ; obj name
					      (mapcar #'(lambda (i)
							  (cdr (assoc i ext-model)))
						      (rest obj-binding))))
				    obj-bindings))
	    
	    ;;(format t "~% model = ~A~% obj-binding = ~A~% obj-model = ~A~%" model obj-bindings obj-model)
	    ;;(finish-output)
	    ;; Model validation
	    (let ((unsatisfied-constraints (remove-if #'(lambda (constraint)
							  (let* ((objects (append (butlast constraint 2) (last constraint)))
								 (mscene (mapcar #'(lambda (v)
										     (find v obj-model :key #'first))
										 objects))
								 (qual-rel (qualifier::qualify-scenario (calculi:calculus-arity calculus)
													:first2all
													calculus
													mscene)))
							    (equal (first qual-rel) constraint)))
						      (first scenario)))) ; scenario ist doppelt eingelistet (warum auch immer)
	      (if unsatisfied-constraints
		  (setq result (format nil "FAILED TO COMPUTE MODEL.~%;; These constraints are not satisfied: ~A~%;; best guess: ~A~%" 
				       unsatisfied-constraints obj-model))
		  (setq model-found? t
			result (format nil "~A~%" obj-model)))))))
      (format stream "~&~a" result)
      obj-model)))

;; test-emptyness
;;
;; low-level entry point to our satisfiability test
;;
(defun test-satisfiability (stream calculus args)
  (let ((slacks (pop args))
	(bindings (mapcar #'(lambda (lst)
			      (cons (first lst) (second lst)))
			  (pop args)))
	(eqns (mapcar #'poly:make-poly args)))
    (when sparq:*debug*
      (format stream "~&;; Slack variables with side condition x_i /= 0: ~{x[~a] ~}" slacks)
      (when bindings
	(format stream "~%;; Initial bindings: ")
	(dolist (b bindings)
	  (format stream "~%;;  x_~a <- ~a" (car b) (cdr b))))
      (format stream "~%;;~%;; Initial set of polynomials:")
      (poly::print-poly-list eqns stream))
    (let ((result (poly:test-emptyness stream eqns slacks :initial-bindings bindings)))
      (cond	((eq result :?) (format stream "~&CANNOT DECIDE.~%"))
		((null result)  (format stream "~&IS SATISFIABLE.~%"))
		(result         (format stream "~&NOT SATISFIABLE.~%"))))))

;; polynomials
;; returns the equations specifying a scenario
(defun polynomials (stream calculus scenario)
  (let ((poly-format (pop scenario))
	(known-formats '(cl-user::text cl-user::lisp cl-user::latex cl-user::cocoa)))
    (unless (member poly-format known-formats)
      (sparq:signal-error "Polynomial export option '~a' unknown - supported formats are: ~{~a, ~} ~a." poly-format (butlast known-formats) (car (last known-formats))))
    (multiple-value-bind (eqns slacks obj-bindings) (a-scenario stream calculus scenario)
      (when (or sparq:*debug* (eq poly-format 'cl-user::text))
	(format stream "~&;; Variable assignment:")
	(format stream "~%;; constraint variable -> object specifiers -> variables")
	(let* ((count 1)
	       (entity-var-names (cdr (assoc (calculi:calculus-basis-entity calculus) *var-names-alist*)))
	       (arity (cdr (assoc (calculi:calculus-arity calculus) '((:binary . 2) (:ternary . 3)))))
	       (var-names (butlast entity-var-names (- 3 arity)))
	       (vars-per-obj (length (first entity-var-names))))
	  (dolist (o (mapcar #'first obj-bindings))
	    (format stream "~%;; ~a~23T-> (" o )
	    (dolist (var (first entity-var-names))
	      (format stream "~a[~a] " o var))
	    (format stream ") ~44T-> (")
	    (dotimes (i vars-per-obj)
	      (format stream "x[~a] " count) 
	      (incf count))
	    (format stream ")")))
	(format stream "~%;;~%;; Slack variables with side condition x_i /= 0: ~{x[~a] ~}~%;;" slacks))
      (case poly-format
	(cl-user::lisp (print slacks)
		       (pprint eqns stream))
	(cl-user::text (poly::print-poly-list eqns stream))
	(cl-user::cocoa  (format stream "~&// slack variables: ~{x[~a], ~}x[~a]" (butlast slacks) (car (last slacks)))
			 (format stream "~%Ideal( ");
			 (let ((last-p (car (last eqns))))
			   (mapc #'(lambda (p)
				     (poly::print-poly p stream)
				     (if (eq last-p p)
					 (format stream " );~%")
					 (format stream " ,~%       ")))
				 eqns)))
	(cl-user::latex (format stream "~&\\begin{eqnarray*}")
			(mapc #'(lambda (e) 
				  (format stream "~%  \\item 0 &=& ")
				  (poly::print-poly-tex e stream))
			      eqns)
			(format stream "~%\\end{eqnarray}"))))))

;; Command dispatcher invoked from SparQ's main command dispatcher when handling "a-reasoning" commands
;;
;; qualify  <metrical scene>   : maps metric scene to qualitative scenario
;; consistency <scenario>      : tests consistency of scenario
;; analyze-operation  <op>     : verifies operation table
;; compute-model <scenario>    : aka. 'quantify'
;; satisfiability <slacks> <bindings> <eqns> : runs test-emptiness on equations
;; polynomials <output-type> <scenario>      : returns polynomials to given scenario
;;
(defun process-command (stream calculus args)
  (unless (calculi::calculus-algebraic-spec calculus)
    (sparq:signal-error "~&Calculus specification of calculus ~a does not provide algebraic specification" (calculi:calculus-name calculus)))
  (cond ((eq (car args) 'cl-user::qualify)
	 (qualify stream calculus (rest args)))
	((eq (car args) 'cl-user::consistency)
	 (a-consistency stream calculus (rest args)))	
	((eq (car args) 'cl-user::analyze-operation)
	 (analyze-operation stream calculus (rest args)))
	((eq (car args) 'cl-user::compute-model)
	 (a-model stream calculus (rest args)))
	((eq (car args) 'cl-user::satisfiability)
	 (test-satisfiability stream calculus (rest args)))
	((eq (car args) 'cl-user::polynomials)
	 (polynomials stream calculus (rest args)))
	((eq (car args) 'cl-user::groebner-basis)
	 (groebner-basis stream calculus (rest args)))
	(t (sparq::signal-error "~&Command '~a' supplied to a-reasoning not supported." (car args)))))


