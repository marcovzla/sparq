;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;; COMPUTE-RELATION  --- package implementing SparQ user
;;; commands for computing with relations
;;;

;;; There is only one important function in this package: compute-relation
;;; This function parses the user's command and invokes the corresponding
;;; functions for computing. Evaluating complex expressions such as e.g. 
;;; (converse (composition r1 r2) r2) is performed by compute-complex-expression
;;; Most of the code in this package is involved with error checking and error
;;; messages. For internal needs of computing with relation, the functions in
;;; calculi.lisp are invoked directly.

;; Change history (most recent first):
;; 2007-01-26 DW  bug fix in read-relation macro wrt. to latest ofunc interface
;; 2007-01-25 DW  adapted to the new architecture of ofuncs and relation-representation as of V0.7
;; 2006-11-02 DW  started history aadapted SparQ's V0.6 compute-relation to new functions in calculi

(defpackage :compute-relation
  (:use :common-lisp :sparq :calculi :ofunc :relations)
  (:export :compute-relation))

(in-package :compute-relation)


;; Macro that iterates over (unordered) pairs
;; (do-pairs (x '(1 2 3)) (y '(a b c)) (print (cons x y))) => (1 . 1) (1 . 2) (1 . 3) (2 . 2) (2 . 3) (3 . 3)
(defmacro do-pairs (vars list &body body)
  (let ((ls1 (gensym))
	(ls2 (gensym))
	(var1 (first vars))	
	(var2 (second vars)))
    `(do ((,ls1 ,list (cdr ,ls1)))
	 ((null ,ls1))
       (let ((,var1 (car ,ls1)))
	 (do ((,ls2 ,ls1 (cdr ,ls2)))
	     ((null ,ls2))
	   (let ((,var2 (car ,ls2)))
	     ,@body))))))

;; Computes the closure of a set of relations
;; If calculus is binary, closure is computed over the operations composition and converse,
;; otherwise (ternary) over the operations composition, inverse, homing, and shortcut

(defun closure (calculus relations)
  (declare (type list relations))
  (let* ((rel-rep (calculus-relation-representation calculus))
	 (func (optimize-for-instance (calculus rel-rep relations)
		   (((composition calculus) (calculi::calculus-composition calculus)) ; Consider these two calls in optimization...
		    (intersect   (relations::relation-representation-intersect rel-rep))
		    ((converse calculus) (calculi::calculus-converse calculus)))
		 
		 (let* ((rel< (symbol-function (relations:relation-representation-< rel-rep)))
			(iters 0)
			(count (length (the list relations)))
			(closure-set (reduce #'(lambda (set relation)
						 (data:r/b-tree-insert set relation rel<))
					     relations
					     :initial-value nil))
			(new-in-closure nil))
		 (declare (type fixnum iters count))

		 (labels ((register (r)
			    (unless (data:r/b-tree-find closure-set r rel<)
			      (push r new-in-closure)
			      (incf count)
			      (setq closure-set (data:r/b-tree-insert closure-set r rel<)))))
		 (when *debug*
		   (format *error-output* "~&;; Computing closure of ~a (a set with ~a relations)~%;; starting at ~a~%" 
			   (mapcar #'(lambda (r)
				       (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r))
				   relations)
			   count
			   (time-string)))
		 ;; Kickoff: relate the set of relations itself
		 ;; individually expand new relations
		 (dolist (r new-in-closure)
		   (register (converse calculus r)))
		 (do-pairs (r1 r2) relations
		   (register (composition calculus r1 r2))
		   (register (composition calculus r2 r1))
		   (register (intersect r1 r2)))
		   
		   ;; Iterate while new relations emerge
		   (loop while new-in-closure do
			(let ((this-round new-in-closure))
			  (when *debug*
			    (finish-output)
			    (format *error-output* ";; Starting iteration #~a with a total of ~a relations (~a new in last iteration) at ~a~%;; -> ~a steps~%" iters count (length new-in-closure) (time-string) (+ (length new-in-closure) (* (length new-in-closure) count) (expt (length new-in-closure) 2)))
			    #|
			    (multiple-value-bind (min sec) (floor (/ (+ (* (length this-round) count) (expt (length this-round) 2)) 
			    149889.0) 60)
			    (format *error-output* ";; I'm guessing this iteration takes about ~a minutes and ~a seconds~%" min sec))			    |#
			    (finish-output *error-output*)
			    (incf iters))
			
			  (setq new-in-closure nil)

			  ;; individually expand new relations
			  (dolist (r this-round)
			    (register (converse calculus r)))
			  ;; relate newly added relations to themselves
			  ;(print "done single expand")
			  
			  (do-pairs (r1 r2) this-round
			    (register (composition calculus r1 r2))
			    (register (composition calculus r2 r1))
			    (register (intersect r1 r2)))

			  ;(print "done new x new")
			  ;; relate 'old' relations to the new ones
			  
			  
			  (dolist (r1 (data:r/b-tree->list closure-set))
			    (dolist (r2 this-round)
			      (register (composition calculus r1 r2))
			      (register (composition calculus r2 r1))
			      (register (intersect r1 r2))))
			  
					;(print "done new x old")
			  ;; iteration done
			  ))
		   (when *debug* 
		     (format *error-output* ";; done at ~a: ~a relations after ~a iterations~%" (time-string) count iters))
		   (data:r/b-tree->list closure-set))))))    
    (funcall func calculus rel-rep relations)))

(defun closure/alt (calculus relations)
  (declare (type list relations))
  (let* ((rel-rep (calculus-relation-representation calculus))
	 (rel< (symbol-function (relations:relation-representation-< rel-rep)))
	 (iters 0)
	 (count (length (the list relations)))
	 (closure-set (reduce #'(lambda (set relation)
				  (data:r/b-tree-insert set relation rel<))
			      relations
			      :initial-value nil))
	 (new-in-closure nil))
    (declare (type fixnum iters count))
    (labels ((combine (r1 r2)
	       (list (calculi:composition  calculus r1 r2)
		     (calculi:composition calculus r2 r1)
		     (calculi:intersect calculus r1 r2)))
	     (expand (r)
	       (list (calculi:converse calculus r)))
			(register (rs)
			  (dolist (r rs)
			    (unless (data:r/b-tree-find closure-set r rel<)
			      (push r new-in-closure)
			      (incf count)
				(setq closure-set (data:r/b-tree-insert closure-set r rel<))))))
		 (when *debug*
		   (format *error-output* "~&;; Computing closure of ~a (a set with ~a relations)~%;; starting at ~a~%" 
			   (mapcar #'(lambda (r)
				       (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r))
				   relations)
			   count
			   (time-string)))
		 ;; Kickoff: relate the set of relations itself
		 ;; individually expand new relations
		 (dolist (r new-in-closure)
		   (register (expand r)))
		   (do-pairs (r1 r2) relations
		     (register (combine r1 r2)))
		   
		   ;; Iterate while new relations emerge
		   (loop while new-in-closure do
			(let (next-round)
			  (when *debug*
			    (format *error-output* ";; Starting iteration #~a with ~a relations at ~a~%" iters count (time-string))
			    (finish-output *error-output*)
			    (incf iters))
			  ;; individually expand new relations
			  (dolist (r new-in-closure)
			    (register (expand r)))
			  ;; relate newly added relations to themselves
			  (do-pairs (r1 r2) new-in-closure
			    (register (combine r1 r2)))
			  ;; relate 'old' relations to the new ones
			  (do ((r1-node (data:r/b-tree-min-node closure-set) (data:r/b-node-successor r1-node)))
			      ((null r1-node))
			    (let ((r1 (data:r/b-node-data r1-node)))
			    (dolist (r2 new-in-closure)
			      (register (combine r1 r2)))))
			;; iteration done
			  (setq new-in-closure next-round)))
		   (when *debug* 
		     (format *error-output* ";; done at ~a: ~a relations after ~a iterations~%" (time-string) count iters))
		   (data:r/b-tree->list closure-set))))

;; Two macros that signal an error to the user if the arity of a calculus isn't
;; OK, e.g. when asking to compute homing in a binary calculus
(defmacro ensure-binary-calculus (calculus &body body)
  `(if (eq (calculus-arity ,calculus) :binary)
     (progn
       ,@body)
     (signal-error "Calculus '~a' is no binary calculus!~%" (calculi:calculus-name ,calculus))))

(defmacro ensure-ternary-calculus (calculus &body body)
  `(if (eq (calculus-arity ,calculus) :ternary)
     (progn
       ,@body)
     (signal-error "Calculus '~a' is no ternary calculus!~%" (calculi:calculus-name ,calculus))))

(defun compute-complex-expression (stream calculus expression)
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))	 
	 (encoder  (relations:relation-representation-encoder rel-rep)))
    (labels ((eval-expression (exp)
	       (if (atom exp)
		   (ofuncall encoder rel-rep exp)
		   (let ((fn (first exp))
			 (args (rest exp)))
		     (let ((func (assoc fn (list (cons 'cl-user::shortcut 'shortcut)
						 (cons 'cl-user::sc 'shortcut)
						 (cons 'cl-user::shortcuti #'(lambda (c r) (inverse c (shortcut c r))))
						 (cons 'cl-user::sci #'(lambda (c r) (inverse c (shortcut c r))))
						 (cons 'cl-user::homing 'homing)
						 (cons 'cl-user::hm 'homing)
						 (cons 'cl-user::homingi #'(lambda (c r) (inverse c (homing c r))))
						 (cons 'cl-user::hmi #'(lambda (c r) (inverse c (homing c r))))
						 (cons 'cl-user::converse 'converse)
						 (cons 'cl-user::cnv 'converse)
						 (cons 'cl-user::inv 'inverse)
						 (cons 'cl-user::inverse 'inverse)
						 (cons 'cl-user::cmpl #'(lambda (c r) (compl c r)))
						 (cons 'cl-user::complement #'(lambda (c r) (compl c r)))))))
		       (if func ; handle unary function
			   (if (null (cdr args))
			       (funcall (cdr func) calculus (eval-expression (car args)))
			       (signal-error "~%Syntax error: more than one argument to unary operation ~a." (car func)))
			   (let ((func (assoc fn (let ((tmp (list (cons 'cl-user::composition 'composition)
								  (cons 'cl-user::union #'(lambda (c r1 r2) (calculi:unite c r1 r2)))
								  (cons 'cl-user::minus #'(lambda (c r1 r2) (calculi:minus c r1 r2)))
								  (cons 'cl-user::isec #'(lambda (c r1 r2) (calculi:intersect c r1 r2)))
								  (cons 'cl-user::intersection #'(lambda (c r1 r2) (calculi:intersect c r1 r2))))))
						   (when (eq :binary (calculus-arity calculus))
						     (push (cons 'cl-user::ncomp 'composition) tmp)
						     (push (cons 'cl-user::n-ary-composition 'composition) tmp))
						   tmp))))
			     (if func ; handle binary function
				 (if (and (cdr args) (null (cddr args)))
				     (funcall (cdr func) calculus (eval-expression (car args)) (eval-expression (cadr args)))
				     (signal-error "~%Syntax error: ~a arguments to binary operation ~a." (length args) (car func)))
				 (let ((func (assoc fn (let ((tmp (list (cons 'cl-user::ternary-composition 'ternary-composition)
									(cons 'cl-user::tcomp 'ternary-composition))))
							 (when (eq :ternary (calculus-arity calculus))
							   (push (cons 'cl-user::n-ary-composition 'ternary-composition) tmp)
							   (push (cons 'cl-user::ncomp 'ternary-composition) tmp))))))
				   (if func ; handle ternary function
				       (if (and (cddr args) (null (cdddr args)))
					   (funcall (cdr func) calculus (eval-expression (car args)) (eval-expression (cadr args)) (eval-expression (caddr args)))
					   (signal-error "~%Syntax error: ~a arguments to ternary operation ~a." (length args) (car func)))
				       (multiple-value-bind (relation error) (ignore-errors (ofuncall encoder rel-rep exp))
					 (if error                             
					     (signal-error "~%Syntax error: Operation ~a unknwown and expression ~a cannot be interpreted as list of relations" fn exp)
					     relation))))))))))))
      (ofuncall (relations:relation-representation-printer rel-rep)
		rel-rep (eval-expression expression) stream))))


(defmacro read-relation (list calculus)
  (let ((r (gensym))
	(rel-rep (gensym)))
    `(let ((,r (if ,list (pop ,list)
                   (sparq:signal-error "Error: At least one more relation required!")))
	   (,rel-rep (calculi:calculus-relation-representation ,calculus)))
       (ofuncall (relations:relation-representation-encoder ,rel-rep)
		 ,rel-rep
		 ,r))))

;; A special operator that performs a test on a calculus. If the test fails for some relation,
;; this is signaled to the user as in this case there might be an error in the calculus definition.
;; Of course we can't tell whether failure of a test really points to an error since the calculus
;; may have some odd properties, e.g. converse is not idempotent.
;; Test for ternary calculi:
;;   (inverse (shortcut r)) ^ 3 = a
;; Test for binary calculi:
;;   (composition r1 r2) == (converse (composition (converse r2) (converse r1)))
(defun do-calculus-test (stream calculus)
  (let* ((ok? t)
	 (rel-rep (calculi:calculus-relation-representation calculus))
	 (decoder (relations:relation-representation-decoder rel-rep))
	 (br-enc  (relations:relation-representation-br-encodings rel-rep))
	 (rel-mapper (relations:relation-representation-mapper rel-rep)))
    (if (eq :ternary (calculi:calculus-arity calculus))
	;; Test for ternary calculi
	(progn 
	  ;; test ternary composition
	  (when (calculi:calculus-n-ary-composition calculus)
	    (let ((test-ok? t))
	      (flet ((rotation (r)
		       (calculi:shortcut calculus (calculi:inverse calculus r)))
		     (decode (r)
		       (ofuncall decoder rel-rep r)))
		(ofuncall rel-mapper
			  #'(lambda (r1-idx)
			      (let ((r1 (svref br-enc r1-idx)))
				(ofuncall rel-mapper 
					  #'(lambda (r2-idx)
					      (let ((r2 (svref br-enc r2-idx)))
						(ofuncall rel-mapper
							  #'(lambda (r3-idx)
							      (let* ((r3 (svref br-enc r3-idx))
								     (comp0 (calculi:ternary-composition calculus r1 r2 r3))
								     (comp1 (rotation comp0))
								     (comp2 (calculi:ternary-composition calculus (rotation r3) (rotation r1) (rotation r2)))
								     (comp3 (calculi:shortcut calculus comp0))
								     (comp4 (calculi:ternary-composition calculus (calculi:shortcut calculus r2) (calculi:shortcut calculus r1) (calculi:shortcut calculus r3))))
								(unless (ofuncall (relations:relation-representation-same-relation? rel-rep) comp1 comp2)
								  (setq test-ok? nil)
								  (format stream "Failed test *(~a, ~a, ~a)^ROT == ~a != ~a == *(~a^ROT ~a^ROT ~a^ROT)~%"
									  (decode r1) (decode r2) (decode r3) (decode comp1)
									(decode comp2) (decode r3) (decode r1) (decode r2)))
								(unless (ofuncall (relations:relation-representation-same-relation? rel-rep) comp3 comp4)
								  (setq test-ok? nil)
								  (format stream "Failed test (sc *(~a ~a ~a)) == ~a != ~a == *( sc ~a, sc ~a, sc ~a)~%"
									  (decode r1)  (decode r2) (decode r3) (decode comp3)
									  (decode comp4) (decode r2)  (decode r1) (decode r3)))))
							  (relations:relation-representation-universal-relation rel-rep))))
					  (relations:relation-representation-universal-relation rel-rep))))
			  (relations:relation-representation-universal-relation rel-rep)))
	      (when test-ok?
		(format stream "~&Tests passed *(r1,r2,r3)^ROT == *(r3^ROT, r1^ROT, r2^ROT) and sc(*(r1,r2,r3)) == *(sc r2, sc r1, sc r3)~%"))))

	    ;; test  r == (inverse (shortcut r))^3
	  (ofuncall rel-mapper
		    #'(lambda (r1-idx)
			(let* ((r1 (svref br-enc r1-idx))
			       (r2 r1))
			  (dotimes (i 3)
			    (setq r2 (calculi:inverse calculus (calculi:shortcut calculus r2))))
			  (unless (equal r2 r1)
			    (setq ok? nil)
			    (format stream "Failed test r == (inverse (shortcut r))^3 for relation ~a, computed ~a~%" 
				  (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r1) 
				  (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r2)))))
		    (relations:relation-representation-universal-relation rel-rep)))
	;; Test for binary calculi
	;; we check properties of relation algebras
	(flet ((decode (r)
		 (ofuncall decoder rel-rep r)))
	  (format stream "~&;; testing non-trivial relation algebra axioms")
	  ;(format stream "~%{{\\fonttbl\\f0\\fmodern\\fcharset77 Courier;}\\f0 ;; \\ul (1) testing identity relation:\\ul0  for all relations r: r o id = id o r = r \\par }")
	  (format stream "~%;; (1) testing identity relation: for all relations r: r o id = id o r = r")
	  (let ((id (ofuncall (relations:relation-representation-encoder rel-rep) rel-rep (calculi:calculus-identity-relation calculus)))
		(violations ()))
	    (ofuncall rel-mapper
		      #'(lambda (r-idx)
			  (let ((r (svref br-enc r-idx)))
			    (when (or (not (ofuncall (relations:relation-representation-same-relation? rel-rep) r (calculi:composition calculus r id)))
				      (not (ofuncall (relations:relation-representation-same-relation? rel-rep) r (calculi:composition calculus id r))))
			      (setq ok? nil)
			      (push r violations))))
		      (relations:relation-representation-universal-relation rel-rep))
	    (if violations
		(format stream "~%;; test FAILED for ~d base relation~:P: ~{~a ~}" (length violations) (mapcar #'decode violations))
		(format stream "~%;; test passed")))
	  ;;
	  (format stream "~%;; (2) testing converse: for all relations r: (converse (converse r)) = r")
	  (let ((violations ()))
	    (ofuncall rel-mapper
		      #'(lambda (r-idx)
			  (let ((r (svref br-enc r-idx)))
			    (unless (ofuncall (relations:relation-representation-same-relation? rel-rep) r (calculi:converse calculus (calculi:converse calculus r)))			      
			      (setq ok? nil)
			      (push r violations))))
		      (relations:relation-representation-universal-relation rel-rep))
	    (if violations
		(format stream "~%;; test FAILED for ~d base relation~:P: ~{~a ~}" (length violations) (mapcar #'decode violations))
		(format stream "~%;; test passed")))
	  ;;
	  (format stream "~%;; (3) testing converse/composition: for all relations r1, r2: (composition r1 r2) == (converse (composition (converse r2) (converse r1)))")
	  (let ((violations ()))
	    (ofuncall rel-mapper
		      #'(lambda (r1-idx)
			  (let ((r1 (svref br-enc r1-idx)))
			    (ofuncall rel-mapper
				      #'(lambda (r2-idx)
					  (let* ((r2 (svref br-enc r2-idx))
						 (r3-1 (calculi:composition calculus r1 r2))
						 (r3-2 (calculi:converse calculus (calculi:composition calculus (calculi:converse calculus r2) (calculi:converse calculus r1)))))
					    (unless (equal r3-1 r3-2)
					      (setq ok? nil)
					      (push (list r1 r2 r3-1 r3-2) violations))))
				      (relations:relation-representation-universal-relation rel-rep))))
		      (relations:relation-representation-universal-relation rel-rep))
	    (if violations
		(progn 
		  (format stream "~%;; test FAILED for ~a relation pair~:P:" (length violations))
		  (dolist (fail violations)
		    (let ((rels (mapcar #'decode fail)))
		      (format stream "~%;;    (composition ~a ~a) = ~a /= ~a = (converse (composition (converse ~a) (converse ~a)))"
			      (first rels) (second rels) (third rels) (fourth rels) (second rels) (first rels)))))
		(format stream "~%;; test passed")))
	    ;;
	    (format stream "~%;; (4) testing for all relations r,s,t: (intersection (composition r s) (converse t)) = () if and only if (intersection (composition s t) (converse r)) = ()")
	    (finish-output stream)
	    (let ((violations ()))
	    (ofuncall rel-mapper
		      #'(lambda (r1-idx)
			  (let ((r1 (svref br-enc r1-idx)))
			    (ofuncall rel-mapper
				      #'(lambda (r2-idx)
					  (let ((r2 (svref br-enc r2-idx)))
					    (ofuncall rel-mapper
						      #'(lambda (r3-idx)
							  (let* ((r3 (svref br-enc r3-idx))
								 (lhs (calculi:intersect calculus (calculi:composition calculus r1 r2) (calculi:converse calculus r3)))
								 (rhs (calculi:intersect calculus (calculi:composition calculus r2 r3) (calculi:converse calculus r1))))
							    (unless (eq (ofuncall (relations:relation-representation-empty-relation? rel-rep) lhs)
									(ofuncall (relations:relation-representation-empty-relation? rel-rep) rhs))
							      (setq ok? nil)
							      (push (list r1 r2 r3 lhs rhs) violations))))
						      (relations:relation-representation-universal-relation rel-rep))))
				      (relations:relation-representation-universal-relation rel-rep))))
		      (relations:relation-representation-universal-relation rel-rep))
	    (if violations
		(progn 
		  (format stream "~%;; test FAILED for ~a relation triples~:P:" (length violations))
		  (dolist (fail violations)
		    (let ((rels (mapcar #'decode fail)))
		      (format stream "~%;;    (intersection (composition ~a ~a) (converse ~a)) = ~a /= ~a = (intersection (composition ~a ~a) (converse ~a))"
			      (first rels) (second rels) (third rels) (fourth rels) (fifth rels) (second rels) (third rels) (first rels)))))
		(format stream "~%;; test passed")))))
    (if ok?
	(format stream "~&Test passed.")
	(format stream "~&Test failed."))))


(defun calculus-analysis (stream calculus)
  (let* ((basis-entity (calculus-basis-entity calculus))
	 (rel-rep (calculus-relation-representation calculus))
	 (base-rels (relations:relation-representation-base-relations rel-rep))
	 (num-rels (relations:relation-representation-num-base-relations rel-rep))
	 (arity (calculus-arity calculus))
	 (obj-params (cadr (assoc basis-entity '((:2d-point 2) (:dipole 4) (:2d-oriented-point 4) (:1d-point 1) (:3d-point 3)))))
	 (can-determine-probs? (and obj-params (calculi::calculus-qualifier calculus)))
	 (probs (if can-determine-probs?
		    ;; if qualify is available we can determine the distribution of probalities that some
		    ;; base-relation occurs by qualifying randomly generated instantiations
		    (let* ((count (make-array num-rels :initial-element 0))
			   (o1 (make-list obj-params)))
		      ;; preset variables that we don't need to change
		      (flet ((rlist ()
			       (loop for i from 1 to obj-params collecting (- (random 20) 10))))
			(dotimes (i obj-params)
			  (setf (nth i o1) i))
			(dotimes (i 100000)
			  (let ((rel (if (eq arity :binary)
					 (funcall (calculi::calculus-qualifier calculus) o1 (rlist))
					 (funcall (calculi::calculus-qualifier calculus) o1 (rlist) (rlist)))))
			    (incf (aref count (position rel base-rels))))))
		      (dotimes (i num-rels)
			(setf (aref count i) (/ (max 1 (aref count i)) 100000.0)))
		      count)
		    ;; assume equal distribution otherwise
		    (make-array num-rels :initial-element (/ 1.0 num-rels)))))

    (let ((icont (coerce (loop for pr across probs collecting (- (log pr num-rels))) 'vector)) ; information content
	  (rel-encs (relations:relation-representation-br-encodings rel-rep)))
      (format stream "~&Estimate of probabilities of relation occurence: ")
      (if can-determine-probs?
	  (loop for br across base-rels
	        for pr across probs 
	        for ic across icont do
	       (format stream "~%~8A : ~4f  (~4f)" br pr ic))
	  (format stream "cannot be determined, assuming equal probability of ~f" (aref probs 0)))
      (format stream "~2%composition table analysis:")
      (loop for r1 across rel-encs do
	   (loop for r2 across rel-encs do
		(let ((comp (ofuncall (calculi::calculus-composition calculus) calculus r1 r2))
		      (ic (log num-rels 2)))
		  (ofuncall (relations:relation-representation-mapper rel-rep) #'(lambda (idx)
										   (setf ic (min ic (aref icont idx))))
			    comp)
		  (format stream "~%~8A ~8A -> ~F" 
			  (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r1) 
			  (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r2)
			  ic))))

      (format stream "~%das war's fuers erste...~%"))))

(defun compute-relation (stream calculus args)
  (let ((operator (and args
                       (pop args)))
	(rel-rep (calculi:calculus-relation-representation calculus)))
    (labels ((print-relation (r)
	       (ofuncall (relations:relation-representation-printer rel-rep)
			 rel-rep r stream)
	       (finish-output stream)))
      (cond ((or (eq operator 'cl-user::self-test)
		 (eq operator 'cl-user::test-properties)) (do-calculus-test stream calculus))
	    ((eq operator 'cl-user::operation-analysis) (calculus-analysis stream calculus))
	    ((listp operator)  (compute-complex-expression stream calculus operator))
	    ((eq operator 'cl-user::base-closure)
	     (let ((cl (closure calculus (coerce (relations:relation-representation-br-encodings (calculus-relation-representation calculus)) 'list))))
	       (format stream "(")
	       (dolist (r cl)
		 (print-relation r))
	       (format stream ")~%")))
	     
	    ((eq operator 'cl-user::closure) 
	     (unless (listp (car args))
	       (signal-error "Argument to closure is not a list.~%Usage: compute-relation <calculus> closure <list-of-relations>"))
	     (let ((cl (closure calculus (mapcar #'(lambda (r) (ofuncall (relations:relation-representation-encoder rel-rep) rel-rep r))
						 (car args)))))
	       (format stream "(")
	       (dolist (r cl)
		 (print-relation r))
	       (format stream ")~%")
	       (finish-output stream)))
	    (t 
	     (let ((relation (read-relation args calculus)))             
	       (if (null operator)
		   (signal-error "~%Usage: sparq compute-relation <CALCULUS> <OPERATOR> <RELATION>~%")
		   (cond ;((eq operator 'cl-user::reflection )
					; (print-relation stream (reflection calculus relation)))
		     
		     ((or (eq operator 'cl-user::converse) (eq operator 'cl-user::cnv))
		      (ensure-binary-calculus calculus
			(print-relation (converse calculus relation))))
		     
		     ((or (eq operator 'cl-user::inverse) (eq operator 'cl-user::inv))
		      (ensure-ternary-calculus calculus
			(print-relation (inverse calculus relation))))
		     
		     ((or (eq operator 'cl-user::shortcut) (eq operator 'cl-user::sc))
		      (ensure-ternary-calculus calculus
			(print-relation (shortcut calculus relation))))
		     
		     ((or (eq operator 'cl-user::shortcuti) (eq operator 'cl-user::sci))
		      (ensure-ternary-calculus calculus
			(print-relation (inverse calculus (shortcut calculus relation)))))
		     
		     ((or (eq operator 'cl-user::homing) (eq operator 'cl-user::hm))
		      (ensure-ternary-calculus calculus
			(print-relation (homing calculus relation))))
		     
		     ((or (eq operator 'cl-user::homingi) (eq operator 'cl-user::hmi))
                      (ensure-ternary-calculus calculus
			(print-relation (inverse calculus (homing calculus relation)))))
		     
		     ((or (eq operator 'cl-user::composition) (eq operator 'cl-user::comp) (eq operator 'cl-user::binary-composition))
		      (let ((relation2 (read-relation args calculus)))
			(print-relation (composition calculus relation relation2))))
		     
		     ((eq operator 'cl-user::union)
		      (let ((relation2 (read-relation args calculus)))
			(print-relation (unite calculus relation relation2))))
		     
		     ((or (eq operator 'cl-user::intersection) (eq operator 'cl-user::isec))
		      (let ((relation2 (read-relation args calculus)))
			(print-relation (calculi:intersect calculus relation relation2))))
		     
		     ((eq operator 'cl-user::minus)
		      (let ((relation2 (read-relation args calculus)))
                        (print-relation (calculi:minus calculus relation relation2))))
		     
		     ((or (eq operator 'cl-user::complement) (eq operator 'cl-user::cmpl))
		      (print-relation (compl calculus relation)))
		     
		     ((or (eq operator 'cl-user::ternary-ary-composition) (eq operator 'cl-user::tcomp))
		      (ensure-ternary-calculus calculus
			(print-relation (ternary-composition calculus relation (read-relation args calculus) (read-relation args calculus)))))		     

		     ((or (eq operator 'cl-user::n-ary-composition) (eq operator 'cl-user::ncomp))
		      (if (eq :binary (calculus-arity calculus))
			  (print-relation (composition calculus relation (read-relation args calculus)))
			  (print-relation (ternary-composition calculus relation (read-relation args calculus) (read-relation args calculus)))))
		     (t               
		      (signal-error "Error: Operator ~a unknown!~%" operator))))))))))

