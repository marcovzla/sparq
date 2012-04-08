;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;; SparQ constraint reasoning
;;;

;; Change history (most recent first):
;; 2009-06-03 DW  added :check option to scenario-consistency
;; 2008-05-30 DW  direct call to reasoner when tractable subset is available
;; 2007-10-10 DW  introduced ternary algebraic closure
;; 2007-03-14 DW  improved scenario-consistency; splitted files
;; 2007-03-13 DW  ofunc-optimized path consistency
;; 2006-10-26 DW  initial version for SparQ V0.7


(in-package :constraint-reasoning)


;; Constraint network matching
(defun find-sub-networks (stream calculus cmd-stream)
  (multiple-value-bind (query-objects query-constraints) (parse-constraint-network calculus cmd-stream)
    (multiple-value-bind (objects constraints) (parse-constraint-network calculus (list (second cmd-stream)))
      ;; resolve name conflicts by renaming objects in the query-network
      (mapc #'(lambda (a)
		(let ((new-a (gensym (string-upcase (format nil "~a-" a)))))
		  (when sparq:*debug*
		    (format stream "~&;; Replacing ~a by ~a in query network" a new-a))
		  (setq query-objects (mapcar #'(lambda (x)
						  (if (eq x a)
						      new-a
						      x))
					      query-objects))
		  (mapcar #'(lambda (x)
			      (when (eq (constraint-object-1 x) a)
				(setf (constraint-object-1 x) new-a))
			      (if (listp (constraint-object-2 x))
				  (setf (constraint-object-2 x) (mapcar #'(lambda (x)
									    (if (eq x a)
										new-a
										x))
									(constraint-object-2 x)))
				  (if (eq (constraint-object-2 x) a) 
				      (setf (constraint-object-2 x) new-a))))
			  query-constraints)))
	    (intersection query-objects objects))
      ;; set up combined network
      (let* ((all-objects (append query-objects objects))
	     (all-constraints (append query-constraints constraints))
	     (rel-rep (calculi:calculus-relation-representation calculus))
	     (id (ofuncall (relations:relation-representation-encoder rel-rep) rel-rep (calculi:calculus-identity-relation calculus)))
	     (matches ()))
	(flet ((binary-callback (objs matrix)
		 ;;(format t "~%")
		 ;;(dump-constraint-matrix stream calculus objs matrix)
		 (let ((match ()))
		   (dolist (qo query-objects)
		     (let ((matched-to (find-if #'(lambda (o)
						    (let ((r (aref matrix (position qo objs) (position o objs))))
						      (equal id r)))
						objects)))
		       (when matched-to (push (list qo matched-to) match))))
		   ;;(format stream "match = ~a" match)
		   (unless (or (null match) (find match matches :test #'equal))
		     (push match matches)
		     (when match
		       (let ((match-list (apply #'append (butlast match))))
			 (format stream "~%~{~a <- ~a, ~}~a <- ~a" match-list (caar (last match)) (cadar (last match)))))))
		 nil)
	       (ternary-callback (constraints)
		 t))
	  (if (eq :binary (calculus-arity calculus)) 
	      ;;(test-consistency/binary stream calculus all-objects all-constraints :first)
	      (if (calculus-tractable-subsets calculus)
		  (tset-scenario-consistency/binary calculus all-objects all-constraints #'binary-callback nil)
		  (scenario-consistency/binary calculus all-objects all-constraints #'binary-callback))
	      (scenario-consistency/ternary calculus all-constraints #'ternary-callback)))
	(unless matches
	  (format stream "~%NO MATCH."))))))

;; Enforcing path-consistency
(defun propagate (stream calculus cmd-stream)
  (with-timing stream
    (multiple-value-bind (objects constraints) (parse-constraint-network calculus cmd-stream)    
      (report-time "network parse/check")
      (cond ((eq :binary (calculus-arity calculus)) (test-pathconsistency/binary stream calculus objects constraints))
	    ((eq :ternary (calculus-arity calculus)) (test-pathconsistency/ternary stream calculus objects constraints))
	    (t (signal-error "Unsupported arity of calculus '~a' ~a; :binary or :ternary are supported.~%" 
			     (calculus-name calculus)  (calculus-arity calculus))))
      (report-time "output result"))))


(defun n-ary-closure (stream calculus cmd-stream)
  (with-timing stream
    (multiple-value-bind (objects constraints) (parse-constraint-network calculus cmd-stream)
      (report-time "network parse/check")
      (cond ((eq :binary (calculus-arity calculus)) (test-pathconsistency/binary stream calculus objects constraints))
	    ((eq :ternary (calculus-arity calculus)) (if (calculi:calculus-n-ary-composition calculus)
							 (test-ternary-closure stream calculus objects constraints)
							 (signal-error "No specification of ternary composition is calculus definition of '~a'" (calculus-name calculus))))
	    (t (signal-error "Unsupported arity of calculus '~a' ~a; :binary or :ternary are supported.~%" 
			     (calculus-name calculus)  (calculus-arity calculus)))))))

;; Enforcing scenario-consistency
(defun scenario-consistency (stream calculus args)
  (let ((solutions (let ((tmp (if args
                                (pop args)
                                (signal-error "Usage: sparq constraint-reasoning <calculus> scenario-consistency { first | all | interactive }~%"))))
                     (cond ((eq tmp 'cl-user::first) :first)
                           ((eq tmp 'cl-user::interactive) :interactive)
                           ((eq tmp 'cl-user::all) :all)
                           ((eq tmp 'cl-user::check) :check)
                           (t (signal-error "Usage: sparq constraint-reasoning <calculus> scenario-consistency { first | all | interactive }~%"))))))
    (with-timing stream
      (multiple-value-bind (objects constraints) (parse-constraint-network calculus args)
	(sparq:report-time "network parse/check")
	(cond
	  ((and (eq :binary (calculus-arity calculus))
		(calculus-tractable-subsets calculus)) (tset-consistency/binary stream calculus objects constraints solutions))
	  ((eq :binary (calculus-arity calculus)) (test-consistency/binary stream calculus objects constraints solutions))
	  ((eq :ternary (calculus-arity calculus)) (test-consistency/ternary stream calculus objects constraints solutions))
	  (t (signal-error "Unsupported arity of calculus '~a' ~a; :binary or :ternary are supported.~%" 
			   (calculus-name calculus)  (calculus-arity calculus))))))))

(defun n-ary-consistency (stream calculus args)
  (let ((solutions (let ((tmp (if args
                                (pop args)
                                (signal-error "Usage: sparq constraint-reasoning <calculus> scenario-consistency { first | all | interactive }~%"))))
                     (cond ((eq tmp 'cl-user::first) :first)
                           ((eq tmp 'cl-user::interactive) :interactive)
                           ((eq tmp 'cl-user::all) :all)
                           (t (signal-error "Usage: sparq constraint-reasoning <calculus> scenario-consistency { first | all | interactive }~%"))))))
    (with-timing stream
      (multiple-value-bind (objects constraints) (parse-constraint-network calculus args)
	(report-time "network parse/check")
	(let ((now2 (get-internal-real-time)))
	  (cond 
	    ((eq :binary (calculus-arity calculus)) (test-consistency/binary stream calculus objects constraints solutions))
	    ((eq :ternary (calculus-arity calculus)) (test-ternary-consistency stream calculus objects constraints solutions))
	    (t (signal-error "Unsupported arity of calculus '~a' ~a; :binary or :ternary are supported.~%" 
			     (calculus-name calculus)  (calculus-arity calculus)))))))))

;; entry point for the "check-consistency" command
(defun check-consistency (stream calculus args)
  (let ((m (calculi:calculus-consistency-method calculus)))
    (cond ((or (eq m :a-closure)
	       (eq m :algebraic-closure))
	   (propagate stream calculus args))
	  
	  ((eq m :n-ary-closure)
	   (n-ary-closure stream calculus args))
	  
	  ((eq m :scenario-consistency)
	   (scenario-consistency stream calculus (cons 'cl-user::check args)))
	  
	  ((eq m :n-ary-scenario-consistency)
	   (n-ary-consistency stream calculus args))
	  
	  (t
	   (signal-error "No decision method for consistency is known for calculus ~a" (calculi:calculus-name calculus))))))

(export '(n-ary-closure n-ary-consistency check-consistency scenario-consistency))