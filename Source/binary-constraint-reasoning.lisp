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
;; 2009-06-12 DW  improved heuristic; macro-inlined queue handling
;; 2009-06-11 DW  bug fix: wrong list when handling tractable subsets
;; 2009-06-03 DW  added :check option to scenario-consistency
;; 2008-09-25 DW  bug fix of bug fix: returning from wrong block in scenario-consistency...
;; 2008-08-26 DW  bug fix in scenario-consistency
;; 2008-06-04 DW  changed tractable subsets to ofuncs
;; 2008-05-30 DW  added tractable subset exploitation
;; 2007-04-17 DW  changed 2do-item struct to positional constructor - saves 0.5 seconds every 10,000,000 calls ;-)
;; 2007-03-15 DW  improved scenario-consitency further; fix with returning from compile-blocks
;; 2007-03-14 DW  improved scenario-consistency; splitted files
;; 2007-03-13 DW  ofunc-optimized path consistency
;; 2006-10-26 DW  initial version for SparQ V0.7

(in-package :constraint-reasoning)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                              ;;;
;;; Binary constraint reasoning  ;;;
;;;                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Prints out a constraint matrix as used in binary constraint reasoning
(defun dump-constraint-matrix (stream calculus objects constraint-matrix)
  "Prints a constraint matrix to standard-out using the object names supplied" 
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (decoder (relations:relation-representation-decoder rel-rep)))
    (format stream "(")
    (dotimes (a (length objects))
      (do ((b 0 (1+ b)))
	  ((>= b a))
	(format stream "(~a ~a ~a)" (nth a objects)  (ofuncall decoder rel-rep (aref constraint-matrix a b)) (nth b objects))))
    (format stream ")~%")
    (finish-output stream)))


;; 2do-items store the arcs we need to check when enforcing pathchonsistency
;; The heuristic value controls which arc to inspect next
#|
(defstruct  (2do-item (:constructor create-2do-item (a b heuristic)))
  (heuristic 0 :type fixnum)
  (a  0 :type fixnum)
  (b  0 :type fixnum))
|#


(declaim (inline create-2do-item))
(defun create-2do-item (a b heuristic)
  (declare (type fixnum a b heuristic)
	   (optimize (speed 3) (safety 0)))
  (logior (the fixnum (ash (max 31 heuristic) 24))
	  (the fixnum (ash a 12))
	  b))

(declaim (inline 2do-item-heuristic))
(defun 2do-item-heuristic (2do)
  (declare (type fixnum 2do)
	   (optimize (speed 3) (safety 0)))
  (ash 2do -24))

(declaim (inline 2do-item-a))
(defun 2do-item-a (2do)
  (declare (type fixnum 2do)
	   (optimize (speed 3) (safety 0)))
  (logand 4095 (ash 2do -12)))

(declaim (inline 2do-item-b))
(defun 2do-item-b (2do)
  (declare (type fixnum 2do)
	   (optimize (speed 3) (safety 0)))
  (logand 4095 2do))


;; Ordering of 2do items for use with r/b-trees
#|
(declaim (inline queue<))
(defun queue< (node1 node2)
  (declare (type 2do-item node1 node2)
	   (optimize (speed 3) (safety 0)))
  (< (the fixnum (2do-item-heuristic node1)) (the fixnum (2do-item-heuristic node2))))
|#

(defmacro push-queue (item min tree)
  `(let (node)
     (multiple-value-setq (,tree node) (data:r/b-tree-insert ,tree ,item #'<))
     (when (or (null ,min)
	       (< ,item (the fixnum (data:r/b-node-data ,min))))
       (setq ,min node))))
  
(defmacro pop-queue (min tree)
  `(when ,min
     (prog1 (data:r/b-node-data ,min)
       (setq ,tree (data:r/b-tree-delete-node ,tree ,min)
	     ,min (data:r/b-node-successor ,min)))))

#|
;; Priority queue of 2do elements based on 
(let ((tree ())
      (min nil))
  (declare (type (or null data:r/b-node) min tree))

  (defun reset-pqueue ()
    (declare (optimize (speed 3) (safety 0)))
    (setq tree ()
	  min nil))

  (declaim (inline push-queue))
  (defun push-queue (item)
    (declare (optimize (speed 3) (safety 0)))
    (multiple-value-bind (tree% node) (data:r/b-tree-insert tree item #'queue<)
      (setq tree tree%)
      (when (or (null min)
		(queue< item (data:r/b-node-data min)))
	(setq min node))))
  
  (declaim (inline pop-queue))
  (defun pop-queue ()
    (declare (optimize (speed 3) (safety 0)))
    (when min
      (prog1 (data:r/b-node-data min)
	(setq tree (data:r/b-tree-delete-node tree min)
	      min (data:r/b-node-successor min)))))

  (declaim (inline queue-empty?))
  (defun queue-empty? ()
    (declare (optimize (speed 3) (safety 0)))
    (null min)))

|#	
	      
;; van-Beek algorithm for computing the algebraic closure of a binary constraint network
;; The two main tricks of getting this done fast is the heuristic function that traverses
;; the network in a failure-first manner. The second trick is the calculus-dependend
;; re-compilation that is performed.

;; The function is wrapped into a closure that allows us to avoid unecessary recompiling
(let ((pathconsistency-fn nil) 
      (compiled-for nil))

(defun pathconsistency/binary (calculus objects constraints)
  "van Beek algorithm for algebraic closure"
  (declare (type list objects constraints)
	   (optimize (speed 3) (safety 0)))
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (func (if (eq compiled-for calculus) ; Check whether we have already compiled an approprite function
		   pathconsistency-fn
		   (prog1 (setq compiled-for calculus
				pathconsistency-fn
				(optimize-for-instance ; Compile a function to be called 
				    ;; The variables passed to the function
				    (calculus rel-rep objects constraints debug?)
				    ;; Optimize these calls:
				    (((composition calculus) (calculi::calculus-composition calculus))
				     (intersect (relations:relation-representation-intersect rel-rep))
				     ((empty-rel? rel-rep) (relations::relation-representation-empty-relation? rel-rep))
				     ((same-rel? rel-rep) (relations::relation-representation-same-relation? rel-rep))
				     ((restrictiveness calculus) (calculi::calculus-restrictiveness calculus))
				     ((converse calculus) (calculi::calculus-converse calculus)))
				  ;; The actual function:
				  (let ((e (relations:relation-representation-empty-relation rel-rep))
					(modified? nil)
					(min nil)
					(queue nil))
				    (declare (type (or null data:r/b-node) min queue)
					     (type boolean modified?))
				    (flet ((decode (r) ; For time being we just use an ordinary call for debugging output
					     (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r)))
				      (multiple-value-bind (idx-lookup number-of-objects)
					  ;; compute lookup for the position of 'object' in the matrix (and count the objects too)
					(let ((ht (make-hash-table))
					      (i  0))
					  (declare (type fixnum i)
						   (type hash-table ht))
					  (dolist (o objects (values ht i))
					    (setf (gethash o ht) i)
					    (incf (the fixnum i))))
					(let ((constraint-matrix (make-array (list number-of-objects number-of-objects)
									     :initial-element (relations:relation-representation-universal-relation rel-rep)))
					      (arc-matrix (make-array (list number-of-objects number-of-objects)
								      :initial-element t :element-type 'boolean)))
					  ;; initialize the constraint matrix with all given constraints
					  ;; (we don't need to set the diagonal since we won't have a look at it anyway)
					  (dolist (constraint constraints)
					    (declare (type constraint constraint))
					    (let ((i1 (gethash (constraint-object-1 constraint) idx-lookup))
						  (i2 (gethash (constraint-object-2 constraint) idx-lookup))
						  (r  (constraint-relation constraint)))
					      (declare (type fixnum i1 i2))
					      (setf (aref constraint-matrix i1 i2) r					   
						    (aref constraint-matrix i2 i1) (converse calculus r))))
					  
					  ;; Initialize the queue of constraints pending to be checked...
					  (dotimes (i number-of-objects)
					    (do ((j (1+ (the fixnum i)) (1+ (the fixnum j))))
						((eq j (the fixnum number-of-objects)))
					      (push-queue (create-2do-item i j (restrictiveness calculus (aref constraint-matrix i j)))
							  min queue)))
					  (report-time "a-closure setup")					  

					  (loop while min do ;;until (queue-empty?) do
					       					       
					       
					     ;; Retrieve next arc to use in propagation
					       (let* ((arc (the fixnum (pop-queue min queue)))
						      (a (2do-item-a arc))
						      (b (2do-item-b arc)))
						 (declare (type fixnum a b)
							  (dynamic-extent arc))
						 (setf (aref arc-matrix a b) nil)
						 ;; Iterate over all possible triangles in the network
						 (dotimes (c (the fixnum number-of-objects))
						   (when (and (not (eq c a)) (not (eq c b)))
						     
						     ;; Part #1: The arc a-b is used to refine the arc b-c
						     (let* ((rel-bc (aref constraint-matrix b c))
							    (rel-bc-new (intersect rel-bc
										   (composition calculus (aref constraint-matrix b a) (aref constraint-matrix a c)))))
						       
						       ;; Debugging output
						       ;; NB we use a parameter 'debug? rather than *debug* to let the compile
						       ;; remove the when during optimize-for-instance
						       (when debug?
							 (format *error-output* ";; Checking ~a->~a:~a = ~a->~a:~a o ~a->~a:~a " 
								 (nth b objects) (nth c objects) (decode rel-bc)
								 (nth b objects) (nth a objects) (decode (aref constraint-matrix b a))
								 (nth a objects) (nth c objects) (decode (aref constraint-matrix a c)))
							 (if (not (same-rel? rel-bc-new rel-bc))
							     (format *error-output* "refining to ~a->~a:~a~%" (nth b objects) (nth c objects) (decode rel-bc-new))
							     (format *error-output* "OK~%"))
							 (finish-output *error-output*))
						       
						       (unless (same-rel? rel-bc-new rel-bc)
							 (when (empty-rel? rel-bc-new)
							   (setf modified? t
								 (aref constraint-matrix b c) e
								 (aref constraint-matrix c b) e)
							   (return-from-function (values nil modified? constraint-matrix)))
							 (let ((i (min b c))
							       (j (max b c)))
							   (declare (type fixnum i j))
							   (unless (aref arc-matrix i j)
							     (setf (aref arc-matrix i j) t)
							     (push-queue (create-2do-item i j (restrictiveness calculus rel-bc-new))
									 min queue)))
							 
							 (setf modified? t
							       (aref constraint-matrix b c) rel-bc-new
							       (aref constraint-matrix c b) (converse calculus rel-bc-new))))
						     
						     (let* ((rel-ac (aref constraint-matrix a c)) ; Part #2: Refining arc a->c
							    (rel-ac-new (intersect rel-ac
										   (composition calculus (aref constraint-matrix a b) (aref constraint-matrix b c)))))
						       ;; Debugging output
						       (when debug?
							 (format *error-output* ";; Checking ~a->~a:~a = ~a->~a:~a o ~a->~a:~a " 
								 (nth a objects) (nth c objects) (decode rel-ac)
								 (nth a objects) (nth b objects) (decode (aref constraint-matrix a b))
								 (nth b objects) (nth c objects) (decode (aref constraint-matrix b c)))
							 (if (not (same-rel? rel-ac-new rel-ac))
							     (format *error-output* "refining to ~a->~a:~a~%" (nth a objects) (nth c objects) (decode rel-ac-new))
							     (format *error-output* "OK~%"))
							 (finish-output *error-output*))
						       
						       (unless (same-rel? rel-ac-new rel-ac)
							 (when (empty-rel? rel-ac-new)
							   (setf modified? t
								 (aref constraint-matrix a c) e
								 (aref constraint-matrix c a) e)
							   (return-from-function (values nil modified? constraint-matrix)))
							 (let ((i (min a c))
							       (j (max a c)))
							   (declare (type fixnum i j))
							   (unless (aref arc-matrix i j)
							     (setf (aref arc-matrix i j) t)
							     (push-queue (create-2do-item i j (restrictiveness calculus rel-ac-new))
									 min queue)))
							 (setf modified? t
							       (aref constraint-matrix a c) rel-ac-new
							       (aref constraint-matrix c a) (converse calculus rel-ac-new))))))))
					  
					  (values t modified? constraint-matrix)))))))
		     (sparq::report-time "compile a-closure")))))
    (funcall func calculus rel-rep objects constraints *debug*)))

) ; end of closure

;;; 
;;; Entry point for path-consistency (algebraic closure)
;;; invoked by the dispatcher 'propagate' in constraint-reasoning.lisp
;;;
(defun test-pathconsistency/binary (stream calculus objects constraints)
  "Test a set of binary constraints for path-consistency" 
  ;;(sb-sprof:start-profiling)
  (multiple-value-bind (ok? modified? constraint-matrix) (pathconsistency/binary calculus objects constraints)
    ;;(sb-sprof:stop-profiling)
    ;(sb-sprof:report)
    ;(force-output)
    (report-time "a-closure")
    (if ok?
      (progn
        (write-line (if modified? "Modified network." "Unmodified network.") stream)
	(let ((output (with-output-to-string  (out)
			(dump-constraint-matrix out calculus objects constraint-matrix))))
	  (format stream "~a" output)
	  (read-from-string output)))
      (progn
        (format stream "Not consistent.~%")
        ;;(dump-constraint-matrix stream calculus objects constraint-matrix)
	nil))))

;; Splits a disjunction of relations into a list of base relations
;; this routine is only used when no tractable subsets are provided
;;
;; rel-rep relation-representation
;; r       relation whose disjunction is to be counted
;; -> list of relations
(defun disjunction-split (rel-rep r)
  (let ((split-set ())
	(enc (relations:relation-representation-br-encodings rel-rep)))
    (ofuncall (relations:relation-representation-mapper rel-rep) 
	      #'(lambda (i)
		  (push (svref enc i) split-set))
	      r)
    split-set))


;; Searches a contraint matrix for a relation to split
;; and returns the indices and the splitting set (nil otherwise)
;; THIS MIGHT INCLUDE SOME HEURISTIC SELECTION PROCESS IN FUTURE VERSIONS
;;
;; rel-rep relation-representation
;; n       number of objects
;; matrix  constraint matrix
(defun find-splitting-set (rel-rep n matrix)
  (declare (type fixnum n))
  (dotimes (i n)
    (do ((j 0 (+ j 1)))
	((eq i j))
      (let ((set (disjunction-split rel-rep (aref matrix i j))))
	(when (cdr set)
	  (return-from find-splitting-set (values set i j)))))))
  
;; Sets up a constraint matrix
;; Returns the matrix and a hash-table to map objects to indices
;; (Mapping the other way around can be done using nth)
;;
;; INPUT:
;; calculus    - calculus to use
;; objects     - a list of object identifiers (symbols)
;; constraints - list of constraint objects
;;
;; OUTPUT (MULTIPLE-VALUES):
;; matrix      - constraint matrix
;; n           - number of objects (= size of matrix)
;;
(defun setup-constraint-matrix (calculus objects constraints)
  (let ((idx-hash (make-hash-table))
	(n 0))
    ;; Setup hash table to quickly index objects
    (dolist (o objects)
      (setf (gethash o idx-hash) n
	    n (+ n 1)))
    ;; Store constraints in matrix
    (let ((matrix (make-array (list n n) :initial-element (relations:relation-representation-universal-relation (calculus-relation-representation calculus)))))
      (dolist (c constraints)
	(let ((i (gethash (constraint-object-1 c) idx-hash))
	      (j (gethash (constraint-object-2 c) idx-hash))
	      (r (constraint-relation c)))
	  (setf (aref matrix i j) r
		(aref matrix j i) (converse calculus r))))
      (values matrix n))))


;; van-Beek algorithm for enforcing path-consistency --- the same as above but without
;; matrix initialization and only one arc in the initial queue. This avoids overhead 
;; when enforcing scenario-consistency
;;
;; The function is wrapped into a closure that allows us to avoid unecessary recompiling
(let ((pathconsistency-fn nil) 
      (compiled-for nil))

;; INPUT:
;; calculus   active calculus
;; matrix     constraint matrix containing the relations
;; i,j        the arc just changed
;; n          size of matrix
;;
;; OUTPUT (MULTIPLE-VALUES):
;; ok?        t iff no inconsistency occured
;; modified?  t iff some arc has been changed
;; matrix     the (destructively!) updated constraint matrix
;;
(defun reenforce-pathconsistency/binary (calculus objects matrix n min queue)
  "van Beek algorithm for algebraic closure"
  (declare (type fixnum n)
	   (type calculi::calculus calculus)
	   (type (array * *) matrix)
	   (optimize (speed 3) (safety 0)))
  (let* ((rel-rep (calculi:calculus-relation-representation calculus))
	 (func (if (eq compiled-for calculus) ; Check whether we have already compiled an approprite function
		   pathconsistency-fn
		   (prog1
		       (setq compiled-for calculus
			     pathconsistency-fn
			     (optimize-for-instance ; Compile a function to be called 
				 ;; The variables passed to the function
				 (calculus objects rel-rep constraint-matrix n min queue)
				 ;; Optimize these calls:
				 (((composition calculus) (calculi::calculus-composition calculus))
				  (intersect (relations:relation-representation-intersect rel-rep))
				  ((empty-rel? rel-rep) (relations::relation-representation-empty-relation? rel-rep))
				  ((same-rel? rel-rep) (relations::relation-representation-same-relation? rel-rep))
				  ((restrictiveness calculus) (calculi::calculus-restrictiveness calculus))
				  ((converse calculus) (calculi::calculus-converse calculus)))
			       ;; The actual function:
			       (let ((e (relations:relation-representation-empty-relation rel-rep)))
				 (flet ((decode (r) ; For time being we just use an ordinary call for debugging output
					  (ofuncall (relations:relation-representation-decoder rel-rep) rel-rep r)))
				   (loop while min do ;;until (queue-empty?) do
				      ;; Retrieve next arc to use in propagation
					(let* ((arc (the fixnum (pop-queue min queue)))
					       (a (2do-item-a arc))
					       (b (2do-item-b arc)))
					  (declare (type fixnum a b))
					  
					  ;; Iterate over all possible triangles in the network
					  (dotimes (c (the fixnum n))
					    (when (and (not (eq c a)) (not (eq c b)))
					      
					      ;; Part #1: The arc a-b is used to refine the arc a-c
					      (let* ((rel-bc (aref constraint-matrix b c))
						     (rel-bc-new (intersect rel-bc
									    (composition calculus (aref constraint-matrix b a) (aref constraint-matrix a c)))))
						
						(unless (same-rel? rel-bc-new rel-bc) ; evil
						  (when (empty-rel? rel-bc-new)
						    (setf (aref constraint-matrix b c) e
							  (aref constraint-matrix c b) e)
						    (return-from-function (values nil constraint-matrix)))
						  (push-queue (create-2do-item b c (restrictiveness calculus rel-bc-new))
							      min queue)					      
						  (setf (aref constraint-matrix b c) rel-bc-new
							(aref constraint-matrix c b) (converse calculus rel-bc-new))))
					      
					      (let* ((rel-ac (aref constraint-matrix a c))
						     (rel-ac-new (intersect rel-ac
									    (composition calculus (aref constraint-matrix a b) (aref constraint-matrix b c)))))

						(unless (same-rel? rel-ac-new rel-ac)
						  (when (empty-rel? rel-ac-new)
						    (setf (aref constraint-matrix a c) e
							  (aref constraint-matrix c a) e)
						    (return-from-function (values nil constraint-matrix)))
						  (push-queue (create-2do-item a c (restrictiveness calculus rel-ac-new))
							      min queue)				      
						  (setf (aref constraint-matrix a c) rel-ac-new
							(aref constraint-matrix c a) (converse calculus rel-ac-new))))))))
				   
				   (values t constraint-matrix)))))
		     (sparq:report-time "compile a-closure reenforce")))))
    (funcall func calculus objects rel-rep matrix n min queue)))
) ; end of closure


;; Copy-matrix copies a matrix of size n*n
(defun copy-matrix (matrix n)
  (declare (type (simple-array * *) matrix)
	   (type fixnum n)
	   (optimize (speed 3) (safety 0)))
  (let ((m (make-array (list n n) :element-type (array-element-type matrix))))
    (dotimes (i n)
      (dotimes (j n)
	(setf (aref m i j) (aref matrix i j))))
    m))

;;;
;;; Enforces scenario-consistency 
;;; The function determines a consistent network that contains only base relations
;;; The supplied callback is called, passing the consistent network. Depending on
;;; the return value, the search continues for the 'next' solution.
;;; 
(defun scenario-consistency/binary (calculus objects constraints callback)  
  (let ((rel-rep (calculus-relation-representation calculus)))
    (labels ((recursive-search (matrix n) 
	       (multiple-value-bind (set i j) (find-splitting-set rel-rep n matrix)
		 (if (cdr set)
		     ;; Try out all splits
		     (dolist (r set)
		       (setf (aref matrix i j) r
			     (aref matrix j i) (converse calculus r))
		       (let ((min nil)
			     (queue nil))
			   ;;(reset-pqueue)
			 (push-queue (create-2do-item i j 0) min queue)
			 (multiple-value-bind (ok? updated-matrix) 			 
			     (reenforce-pathconsistency/binary calculus 
							       objects
							       (copy-matrix matrix n) 
							       n
							       min
							       queue)
			   (when ok?
			     (recursive-search updated-matrix n)))))
		     ;; We have found a solution
		     (when (funcall callback objects matrix)
		       (return-from scenario-consistency/binary))))))
      
      ;; When enforcing pathconsistency start with applying pathconsistency
      ;; We don't use the standard method but call 'our own' enforce-pathconsistency
      ;; so the function gets compiled only once (saves 0.5 secs)
      ;; Set up a list of arcs to check (here: all!)
      (multiple-value-bind (matrix n) (setup-constraint-matrix calculus objects constraints)
	;;(reset-pqueue)
	(let ((min nil)
	      (queue nil))
	  (dotimes (i n)
	    (do ((j 0 (+ j 1)))
		((eq j i))
	      (push-queue (create-2do-item i j (restrictiveness calculus (aref matrix i j))) min queue)))
	  ;; Enforce path-consistency
	  (multiple-value-bind (ok? matrix) (reenforce-pathconsistency/binary calculus objects matrix n min queue)
	    (when ok?
	      (recursive-search matrix n))))))))
    

#|
;; Takes a list of constraints and complements them by adding
;; constraints with universal relations between unrelated objects
;; WELL, WE MIGHT GET RID OF THIS FUNCTION SOMEWHAT
(defun expand-constraints/binary (objects calculus constraints)
  "Expands a list of constraint such that the constraint network is complete" 
  (let ((accu constraints)
	(u (relations:relation-representation-universal-relation (calculi:calculus-relation-representation calculus))))
    (do ((o1s objects (cdr o1s)))
        ((null o1s))
      (do ((o2s (cdr o1s) (cdr o2s)))
          ((null o2s))
        (let ((os (list (car o1s) (car o2s))))
          (unless (some #'(lambda (c)
                            (null (set-difference os (list (constraint-object-2 c) (constraint-object-1 c)))))
                        accu)
            (when *debug*
              (format *error-output* "~%; Adding constraint (~a * ~a)" (car o1s) (car o2s)))
            (push (make-constraint :object-1 (car o1s)
                                   :object-2 (car o2s)
                                   :relation u)
                  accu)))))
    accu))
|#

(defun test-consistency/binary (stream calculus objects constraints solutions)
  "Checks a constraint network for global consistency" 
  (let ((solution? nil)
	(count 0)
        (canceled? t))
    ;; Define some callbacks that allow the user to retrieve one or more answers
    (flet ((interactive-callback (objects network)
             (dump-constraint-matrix stream calculus objects network)
             (setq solution? t)
	     (incf count)
             (write-line "Solution found. Continue search? (yes / no)" stream)
             (clear-input stream)
             (let ((in (string-downcase (read-line stream nil nil nil))))
	       (loop while (and (string/= "yes" in)
				(string/= "no" in)) do
		    (write-line "Please answer 'yes' or 'no'" stream)
		    (setq in (string-downcase (read-line stream nil nil nil))))
               (setq canceled? (string/= "yes" in))))
           (check-callback (objects network)
	     (declare (ignore objects network))
	     (format stream "~&Consistent.")
             (setq solution? t))
           (first-callback (objects network)
             (setq solution? t)
             (dump-constraint-matrix stream calculus objects network)
             t)
           (all-callback (objects network)
	     (incf count)
             (setq solution? t)
             (dump-constraint-matrix stream calculus objects network)
             nil))
      ;; Call the test
      (scenario-consistency/binary calculus objects constraints ;(expand-constraints/binary objects calculus constraints) 
				   (case solutions
				     (:first #'first-callback)
				     (:check #'check-callback)
				     (:interactive #'interactive-callback)
				     (:all #'all-callback)))
      ;; See whether the callback has been called and print out result
      (if solution?
	  (when (or (eq solutions :all) (not canceled?))
	    (format stream "~D scenario~:P found, no further scenarios exist.~%" count))
	  (write-line "Not consistent." stream)))))


;;;; 
;;;; DEALING WITH TSETS
;;;;

;; the core function for computing consistency using tractable sets
(defun tset-scenario-consistency/binary (calculus objects constraints callback check-only?)
  (declare (optimize (speed 3) (safety 0)))
  (let ((descends 0)
	(ascends 0)
	(early-split-exit 0)
	(split/of (calculi::calculus-tractable-subsets calculus)))
    (declare (type fixnum ascends descends early-split-exit))
    (labels (
	     ;; suchen der naechsten aufzuteilenden relation
	     (next-split (n matrix)
	       (declare (type fixnum n)
			(type (simple-array * *) matrix))
	       (let ((bestset-score MOST-NEGATIVE-FIXNUM)
		     (i (random n))
		     (best-i 0)
		     (best-j 0)
		     (bestset ()))
		 (declare (type fixnum bestset-score best-i best-j i)
			  (type list bestset))
		 (dotimes (i% n)
		   (incf i)
		   (when (eq i n)
		     (setq i 0))
		     (do ((j 0 (1+ j)))
			 ((eq i j))
		       (let ((set (ofuncall split/of 0 (aref matrix i j))))			 
			 (declare (type cons set))
			 (when (< 1 (the fixnum (car set))) ; ein echter split
			   (let ((score (the fixnum (second set))))
			     (declare (type fixnum score))
			     (if (<= early-split-exit score) ;; sofort abbrechen, wenn 'gewinnversprechend'
				 (progn
				   (setq early-split-exit (ash (+ early-split-exit score) -1)) ; erwartungen anpassen
				   (return-from next-split (values (third set) i j)))
				 (when (< bestset-score score)
				   (setq bestset-score score
					 best-i i
					 best-j j
					 bestset set))))))))
		 (when bestset
		   (setq early-split-exit bestset-score)
		   (values (third bestset) best-i best-j))))
	     
	     ;; rekursive suche
	     (recursive-search (matrix n) 
	       (multiple-value-bind (set i j) (next-split n matrix)	       
		 (unless set ; if no untractable relation is there anymore, we split any
		   ;; we now know the network to be consistent, so don't need the dolist
		   ;; actually
		   (when check-only? ;; fast exit when we only need to check consistency
		     (funcall callback objects matrix)
		     ;;(format t "~%DESCENDS = ~a    ASCENDS = ~a~%" descends ascends)
		     (return-from tset-scenario-consistency/binary))
		   (multiple-value-setq (set i j) (find-splitting-set (calculus-relation-representation calculus) n matrix)))
		 ;;(when (and sparq:*debug* set)
		 ;;  (format t "~%splitting ~a <-> ~a" (nth i objects) (nth j objects)))
		 (if set
		     ;; Try out all splits
		     (dolist (r set (incf ascends))
		       (incf descends)
		       (setf (aref matrix i j) r
			     (aref matrix j i) (converse calculus r))
		       ;;(reset-pqueue)
		       (let ((min nil)
			     (queue nil))
			 (push-queue (create-2do-item i j 0) min queue)
			 (multiple-value-bind (ok? updated-matrix) 
			     (let ((m (copy-matrix matrix n)))
			       (declare (dynamic-extent m))
			       (reenforce-pathconsistency/binary calculus 
								 objects
								 m
								 n
								 min
								 queue))
			   (when ok?
			     (recursive-search updated-matrix n)))))
		     ;; We have found a solution
		     (when (funcall callback objects matrix)
		       ;;(format t "~%DESCENDS = ~a    ASCENDS = ~a~%" descends ascends)
		       (return-from tset-scenario-consistency/binary))))))
      
      ;; When enforcing pathconsistency start with applying pathconsistency
      ;; We don't use the standard method but call 'our own' enforce-pathconsistency
      ;; so the function gets compiled only once (saves 0.5 secs)
      ;; Set up a list of arcs to check (here: all!)
      (multiple-value-bind (matrix n) (setup-constraint-matrix calculus objects constraints)
	;;(reset-pqueue)
	(let ((min nil)
	      (queue nil))
	  (dotimes (i n)
	    (do ((j 0 (+ j 1)))
		((eq j i))
	      (push-queue (create-2do-item i j (restrictiveness calculus (aref matrix i j))) min queue)))
	
	  ;; Enforce path-consistency
	  (multiple-value-bind (ok? matrix) (reenforce-pathconsistency/binary calculus objects matrix n min queue)
	    (when ok?
	      (recursive-search matrix n)))
	  ;;(format t "~%;; DESCENDS = ~a    ASCENDS = ~a~%" descends ascends)
	  )))))

;; computes consistency using tractable subsets
;; this is the wrapper function...
(defun tset-consistency/binary (stream calculus objects constraints solutions)
  (let ((solution? nil)
	 (count 0)
	 (canceled? t))
    ;; Define some callbacks that allow the user to retrieve one or more answers
    (labels (
	     #|
	     (count-scens (matrix) ; poor bypassing of relations, should really use a new ofunc for this...
	       (if (sb-int::fixnump (aref matrix 0 0))
		   (let ((n (array-dimension matrix 0))
			 (rels ()))
		     (do ((i 0 (1+ i)))
			 ((>= i n))
		       (do ((j (1+ i) (1+ j)))
			   ((>= j n))
			 (push (logcount (aref matrix i j)) rels)))
		     (apply #'* rels))
		   (let ((n (array-dimension matrix 0))
			 (rels ()))
		     (do ((i 0 (1+ i)))
			 ((>= i n))
		       (do ((j (1+ i) (1+ j)))
			   ((>= j n))
			 (push (apply #'+ (mapcar #'logcount (aref matrix i j))) rels)))
		     (apply #'* rels))))
	     |#
	       (interactive-callback (objects network)
	       (dump-constraint-matrix stream calculus objects network)
	       (setq solution? t)
	       (incf count)
	       (format stream "Continue search? (yes / no)")
	       (clear-input stream)
	       (let ((in (string-downcase (read-line stream nil nil nil))))
		 (loop while (and (string/= "yes" in)
				  (string/= "no" in)) do
		      (write-line "Please answer 'yes' or 'no'" stream)
		      (setq in (string-downcase (read-line stream nil nil nil))))
		 (setq canceled? (string/= "yes" in))))
	     (first-callback (objects network)
	       (setq solution? t)
	       (dump-constraint-matrix stream calculus objects network)
	       t)
	     (check-callback (objects network)
	       (declare (ignore objects network))
	       (format stream "~&Consistent.")
	       (setq solution? t))
	     (all-callback (objects network)
	       (incf count 1 #|(count-scens network)|# )
	       (setq solution? t)
	       (dump-constraint-matrix stream calculus objects network)
	       ;; DEBUG
	       #|
	       (let ((i 0)
		     (j 0)
		     net)
		 (dolist (o1 objects)
		   (setq j 0)
		   (dolist (o2 objects)
		     (push (make-constraint i j (aref network i j)) net)))
		 (format stream "VAL = ~a~%" (pathconsistency/binary calculus objects constraints)))
	       |#
	       nil))
      ;; Call the test
      (tset-scenario-consistency/binary calculus objects constraints ;(expand-constraints/binary objects calculus constraints) 
					(case solutions
					  (:first #'first-callback)
					  (:check #'check-callback)
					  (:interactive #'interactive-callback)
					  (:all #'all-callback))
					(eq solutions :check))
      ;; See whether the callback has been called and print out result
      (sparq:report-time "scenario-consistency")
      (if solution?
	  (when (or (eq solutions :all) (not canceled?))
	    (format stream "~D scenario~:P found, no further scenarios exist.~%" count))
	  (write-line "Not consistent." stream)))))
  
(export '(tset-consistency/binary))