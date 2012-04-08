;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;;
;;; 'Main' function of SparQ - dispatcher
;;; 

;; Change history (most recent first):
;; 2010-02-08 JOW  included neighborhood-reasoning support
;; 2006-10-27 DW   after 0.6 branch is split of we're heading towards 0.7: new calculi & relation representation
;

(in-package :sparq)

;; SparQ state

(defstruct sparq-state 
  (calculus nil)
  (results nil)
  (bindings nil)
  (environment nil))

(defun variable-binding (state var)
  (let ((pair (assoc var (sparq-state-bindings state))))
    (if pair
	(cdr pair)
	:unbound)))

(defun (setf variable-binding) (new-val state variable)
  (let ((pair (assoc variable (sparq-state-bindings state))))
    (if pair
	(setf (cdr pair) new-val)
	(push (cons variable new-val) (sparq-state-bindings state)))))

(defun activate-calculus (cmd-stream state stream)
  (let ((csym (let ((*readtable* sparq:*sparq-readtable*)) (read cmd-stream nil nil))) ;case-sensitive read since this might be a filename...
	(error nil)
	(calculus (sparq-state-calculus state)))
    (unless (symbolp csym)
      (signal-error "'~a' is no valid calculus specifier." csym))
    (if (eq csym 'cl-user::*)
	(setq error (if (not calculus) "No calculus loaded - use of '*' calculus identifier not allowed"))
	; Schoen waere, das Laden zu unterbinden, falls das Kalkuel schon geladen ist, also im current-state steht
	; Dafuer muesste man aber mit verschiedenen Namen Umgehen: DRA-24, dipole-coarse, "Dipol Relation Algebra (DRA)"
	; Das scheint etwas schwierig zu sein
	(unless nil ;(and calculus (string= (calculi:calculus-name calculus) (symbol-name csym)))
	  (progn
	    (setq error (catch 'error (prog1 nil (calculi:load-calculus (symbol-name csym)))))
	    (setq calculus calculi:*calculus*))))
    (if error
	(progn (format stream "An error occured: ~a" error)
	       nil)
	calculus)))

(defun split-string (string char)
  "returns a list of words by splitting string wherever char occurs - zero-length words are ignored"
  (let ((len (length string))
	(pos 0))
    (if (= len 0)
	()
	(progn
	  (loop while (and (< pos len) (char/= (char string pos) char)) do
	       (incf pos))
	  (if (= pos 0)
	      (split-string (subseq string 1) char)
	      (if (< pos len)
		  (cons (subseq string 0 pos) (split-string (subseq string (+ pos 1)) char))
		  (list (subseq string 0 pos))))))))

;; main function for performing single sparq commands in SparQ's interactive mode
(defun handle-command/interactive (command-line stream state)
  (let* ((words (split-string command-line #\Space))
	 (result :no-value)
	 (error (catch 'error (prog1 nil
			       (let* ((command (reduce #'(lambda (line word)
							   (if (and (< 0 (length word))
								    (char= #\$ (char word 0)))
							       (let ((value (variable-binding state (read-from-string (subseq word 1) nil nil))))
								 (concatenate 'string line " " (format nil "~A " value)))
							       (concatenate 'string line " " word)))
						       words
						       :from-end nil
						       :initial-value ""))
				      (cmd-stream (make-string-input-stream command))
				      (cmd (read cmd-stream nil nil)))

				 (cond ;; qualify
				       ((eq cmd 'cl-user::qualify) 
					(let ((calculus (activate-calculus cmd-stream state stream)))
					  (when calculus 
					    (setq result (qualifier:qualify calculus cmd-stream stream state)))))
				       
				       ;; quantify
				       ((eq cmd 'cl-user::quantify) 
					(let ((calculus (activate-calculus cmd-stream state stream)))
					  (when calculus
					    (let ((command (read cmd-stream nil +nothing+))
						  (tmp ())
						  (eof? nil))
					      (loop until eof? do
						   (let ((cmd (read cmd-stream nil +nothing+)))
						     (if (eq cmd +nothing+)
							 (setq eof? t)
							 (push cmd tmp))))
					      (finish-output)
					      (if (listp command) ; constraint-network? (no command)
						  (setq result (quantifier:quantify-scenario stream calculus nil (nreverse (cons command tmp))))
						  (setq result (quantifier:quantify-scenario stream calculus command (nreverse (cons command tmp)))))))))

				       ;; help
				       ((eq cmd 'cl-user::help) (write-line "SparQ commands:" stream)
					(write-line "===============" stream)
					(write-line "QUALIFY <calculus> scene " stream)
					(write-line "    maps quantitative scene to a qualitative constraint network" stream)
					(write-line "QUANTIFY <calculus> <op> scenario" stream)
					(write-line "    computes valuation for consistent scenario" stream)
					(write-line "COMPUTE-RELATION <calculus> expression" stream)
					(write-line "    calculus-algebraic operations" stream)
					(write-line "CONSTRAINT-REASONING <calculus> <op> QCSP..." stream)
					(write-line "    qualitative constraint reasoning" stream)
					(write-line "A-REASONING <calculus> <op> ..." stream)
					(write-line "    algebraic reasoning operations" stream)
					(write-line "CURRENT-CALCULUS" stream)
					(write-line "    prints out calculus currently loaded" stream)
					(write-line "LOAD-CALCULUS <name>" stream)
					(write-line "    load calculus" stream)
					(write-line "LET <var> = <expr>" stream)
					(write-line "    define variables" stream)
					(write-line "EXPORT <calculus> <format> <filename>" stream)
					(write-line "    exports calculus definitions" stream)
					(write-line "QUIT" stream)
					(write-line "    exit SparQ" stream))
				       
				       ;; constraint-reasoning
				       ((eq cmd 'cl-user::constraint-reasoning)
					(let ((calculus (activate-calculus cmd-stream state stream)))
					  (when calculus
					    (let (tmp
						  eof?)
					      (loop until eof? do
						   (let ((cmd (read cmd-stream nil +nothing+)))
						     (if (eq cmd +nothing+)
							 (setq eof? t)
							 (push cmd tmp))))
					      (setq tmp (nreverse tmp))
					      (let ((command (and tmp (pop tmp))))
						(cond ((member command '(cl-user::path-consistency cl-user::a-closure cl-user::algebraic-closure))
						       (setq result (constraint-reasoning:propagate stream calculus tmp)))

						      ((eq command 'cl-user::scenario-consistency) 
						       (let ((result (constraint-reasoning:scenario-consistency stream calculus tmp)))
							 (setq result (sparq-state-results state))))

						      ((eq command 'cl-user::n-ary-scenario-consistency) 
						       (setq result (constraint-reasoning:n-ary-consistency stream calculus tmp)))

						      ((eq command 'cl-user::n-ary-closure)
						       (setq result (constraint-reasoning:n-ary-closure stream calculus tmp)))
						      
						      ((or (eq command 'cl-user::merge)
							   (eq command 'cl-user::refine))
						       (setq result (constraint-reasoning:refine-configurations stream calculus tmp)))

						      ((eq command 'cl-user::extend)
						       (setq result (constraint-reasoning:extend-configurations stream calculus tmp)))

						      ((eq command 'cl-user::check-consistency)
						       (setq result (constraint-reasoning:check-consistency stream calculus tmp)))
						      
						      (t (format stream "An error occured: The command '~a' supplied to constraint-reasoning is unknown!" command))))))))
				       
				       ;; compute-relation
				       ((eq cmd 'cl-user::compute-relation) 
					(let ((calculus (activate-calculus cmd-stream state stream)))
					  (when calculus
					    (let (tmp
						   eof?)
					      (loop until eof? do
						   (let ((cmd (read cmd-stream nil +nothing+)))
						     (if (eq cmd +nothing+)
							 (setq eof? t)
							  (push cmd tmp))))
					      (setq result (compute-relation:compute-relation stream calculus (nreverse tmp)))))))
				       
				       ;; algebraic reasoning
				       ((eq cmd 'cl-user::a-reasoning)
					(let ((calculus (activate-calculus cmd-stream state stream))
					      tmp
					      eof?)
					  (loop until eof? do
						(let ((cmd (read cmd-stream nil +nothing+)))
						  (if (eq cmd +nothing+)
						      (setq eof? t)
						      (push cmd tmp))))
					   (setq result (a-reasoning:process-command stream calculus (nreverse tmp)))))

				       ;; neighborhood reasoning
				       ((eq cmd 'cl-user::neighborhood-reasoning) 
					(let ((calculus (activate-calculus cmd-stream state stream)))
					  (when calculus
					    (let (tmp
						   eof?)
					      (loop until eof? do
						   (let ((cmd (read cmd-stream nil +nothing+)))
						     (if (eq cmd +nothing+)
							 (setq eof? t)
							  (push cmd tmp))))
					      (setq result (neighborhood-reasoning:neighborhood-reasoning stream calculus (nreverse tmp)))))))
							

				       ;; query current-calculus
				       ((eq cmd 'cl-user::current-calculus)
					(if (sparq-state-calculus state)
					    (format stream "Current calculus is ~a.~%" (calculi:calculus-name (sparq-state-calculus state)))
					    (format stream "No calculus loaded.~%")))         
				       
				       ;; load-calculus
				       ((eq cmd 'cl-user::load-calculus) 
					(let ((calculus (activate-calculus cmd-stream state stream)))
					   (when calculus
					     (setf (sparq-state-calculus state) calculi:*calculus*))))

				       ;; calculus export
				       ((eq cmd 'cl-user::export)
					(let ((calculus (activate-calculus cmd-stream state stream))
					      tmp
					      eof?)
					  (loop until eof? do
						(let ((cmd (read cmd-stream nil +nothing+)))
						  (if (eq cmd +nothing+)
						      (setq eof? t)
						      (push cmd tmp))))
					  (export:export-calculus stream calculus (nreverse tmp))))

				       ;; break into lisp (for debugging purposes)
				       ((eq cmd 'cl-user::break)
					(break))

				       ;; let <var> = <expression>
				       ((eq cmd 'cl-user::let)
					(let ((var (read cmd-stream nil nil)) ; obs: read won't stop at '=' in "let foo=23"
					      ;; note: we should *really* use a different reader for user input!
					      =
					      expr)
					  (if (find #\= (symbol-name var))
					      (let* ((sname (symbol-name var))
						     (=pos (position #\= sname)))
						(setq = '=
						      expr (read-line (make-concatenated-stream (make-string-input-stream (format nil "~A " sname) (+ 1 =pos))
												cmd-stream)
								      nil "")
						      var (intern (subseq sname 0 =pos))))
					      (progn
						(setq = (read cmd-stream nil nil))
						(if (< 1 (length (symbol-name =))) ; no space between "=" and right hand side
						    (setq expr (read-line (make-concatenated-stream (make-string-input-stream (format nil "~A " =) 1)
												    cmd-stream)
									  nil "")
							  = '=)						    
						    (setq expr (read-line cmd-stream nil "")))))
					  (if (and (symbolp var)
						   (eq = '=))
					      (progn
						(loop while (and (< 0 (length expr)) (char= #\Space (char expr (- (length expr) 1)))) do
						     (setq expr (subseq expr 0 (- (length expr) 1))))
						(let ((tmp (cond ((string= expr "*")
								  (first (sparq-state-results state)))
								 ((string= expr "**")
								  (second (sparq-state-results state)))
								 ((string= expr "***")
								  (third (sparq-state-results state)))
								 ((char= (char expr 0) #\()
								  (read-from-string expr nil nil))
								 (t (handle-command/interactive expr stream state)))))
						  (when (and (not (eq tmp :error)) (not (eq tmp :no-value)))
						    (setf (variable-binding state var) tmp
							  result tmp))))
					      (format stream "~%ERROR: Syntax of let: let variable = expression~%"))))
				       
				       ((eq cmd 'cl-user::get)
					(let* ((var (read cmd-stream nil nil))
					       (val (variable-binding state var)))
					  (unless (eq val :unbound)
					    (setq result val))
					  (format stream "~%~A == ~A" var val)))

				       (t (format stream "~%ERROR: Command ~a not understood!~%" command)))
				 (finish-output stream))))))
    (if error
	(progn
	  (format stream "An error occured: ~a~%" error)
	  :error)
	result)))


(defun sparq-interactive (stream)
  (format stream ";; SparQ is at your service!")
  (let ((continue? t)
        (state (make-sparq-state)))
    (loop while continue? do
          (format stream "~%sparq> ")
          (finish-output stream)
          (let ((command ""))
	    (multiple-value-bind (dummy error) (ignore-errors (setq command (read-line stream nil "")))
	      (declare (ignore dummy))
	      (when error
		(format stream "A reader error occured (e.g., unmatched paranthesis)~%")))
	    (when (stringp command) (setq command (nstring-downcase command)))
	    (when *debug*
	      (format *error-output* "Received request '~a'~%" command))
	    (if (and (stringp command) (< 3 (length command)) (string= command "quit" :end1 4))
		(progn
		  (setq continue? nil)
		  (format stream "~%Tschuess!~%"))
		(when (and (stringp command)
			   (string/= command ""))
		  (let ((result (handle-command/interactive command stream state)))
		    (unless (eq result :no-value)
		      (push result (sparq-state-results state))
		      (when (cddr (sparq-state-results state))
			(setf (cddr (sparq-state-results state)) ())))))))))
  (finish-output stream))

(defun print-usage ()
  (write-line " Usage:")
  (write-line "      sparq [options] [command]")
  (write-line " Options:")
  (write-line "      -v / --verbose      Turn on debugging output")
  (write-line "      -h / --help         This help message")
  (write-line "      -i / --interactive  Start interactive mode")
  (write-line "      -p / --port         Run sparQ via TCP/IP mode (interactive mode only)")
  (write-line " Commands:")
  (write-line "       compute-relation <CALCULUS> arg-1 ...")
  (write-line "       constraint-reasoning <CALCULUS> <COMMAND> arg-1 ...")
  (write-line "       qualify <CALCULUS> arg-1 ...")  
  (write-line "       quantify <CALCULUS> <OPTIONAL COMMAND> <SCENARIO>")  
  (write-line "       a-reasoning <CALCULUS> arg-1 ...")  
  (write-line "       export <CALCULUS> <format> ..."))

(defun posix-args->lisp (args)
  (let ((in (make-string-input-stream (format nil "~{~a ~}" args)))
        lisp-args
        (reading? t))
    (loop while reading? do
         (let ((sym (read in nil sparq:+nothing+)))
           (if (eq sym sparq:+nothing+)
               (setq reading? nil)
               (push sym lisp-args))))
    (nreverse lisp-args)))

(defun sparq-single-computation (args)
  (let ((command (and args (string-downcase (pop args))))
        (calculus (and args (pop args))))
    (if (or (null calculus)
            (null command))
	;; Complain when we don't know what to do
	(progn
	  (print-usage)
	  (signal-error "Command not understood.~%"))
	;; Figure out the calculus to use
	(let ((error (catch 'error (prog1 nil (calculi:load-calculus calculus)))))
	  (if error
	      (signal-error "~a" error)
	      (progn
		(setq args (posix-args->lisp args))
		(cond
		  ((string= command "compute-relation") (compute-relation:compute-relation *standard-output* calculi:*calculus* args))
		  ((string= command "export") (export:export-calculus *standard-output* calculi:*calculus* args))
		  ((string= command "quantify") (if (listp (first args))
						    (quantifier:quantify-scenario *standard-output* calculi:*calculus* nil args)
						    (quantifier:quantify-scenario *standard-output* calculi:*calculus* (first args) (cdr args))))
		  
		  ((string= command "qualify")
		   (qualifier:qualify calculi:*calculus* 
				      (if args
					  (make-concatenated-stream (make-string-input-stream (format nil "~{~a~}~%" args))
								    *standard-input*)
					  *standard-input*)
				      *standard-output* 
				    nil))
		  ((string= command "constraint-reasoning") (let ((command (and args (pop args)))
								  (gout ()))
							      (when (eq command 'cl-user::-graphviz)
								(setq gout (pop args)
								      command (pop args)))
							      (let ((result (cond ((member command '(cl-user::path-consistency cl-user::a-closure cl-user::algebraic-closure)) 
										   (constraint-reasoning:propagate *standard-output* calculi:*calculus* args))								  
										   ((eq command 'cl-user::scenario-consistency) (constraint-reasoning:scenario-consistency (make-two-way-stream *standard-input* *standard-output*) calculi:*calculus* args))
										   ((eq command 'cl-user::n-ary-scenario-consistency) (constraint-reasoning:n-ary-consistency (make-two-way-stream *standard-input* *standard-output*) calculi:*calculus* args))
										   ((eq command 'cl-user::n-ary-closure) (constraint-reasoning:n-ary-closure (make-two-way-stream *standard-input* *standard-output*) calculi:*calculus* args))
										   ((eq command 'cl-user::check-consistency) (constraint-reasoning:check-consistency (make-two-way-stream *standard-input* *standard-output*) calculi:*calculus* args))
										   ((or (eq command 'cl-user::merge)
											(eq command 'cl-user::refine))
										    (constraint-reasoning:refine-configurations *standard-output* calculi:*calculus* args))
										   ((eq command 'cl-user::extend)
										    (constraint-reasoning:extend-configurations *standard-output* calculi:*calculus* args))
										   ((eq command 'cl-user::match)
										    (constraint-reasoning::find-sub-networks *standard-output* calculi:*calculus* args))
										   (t (signal-error "The command '~a' supplied to constraint-reasoning is unknown!~%" command)))))
								(when (and gout (listp result) (eq :binary (calculi:calculus-arity calculi:*calculus*)))
								  (with-open-file (graph gout :direction :output :if-exists :supersede)
								    (format graph "digraph {~%")
								    (mapc #'(lambda (edge)
									      (format graph "~a -> ~a~%" (first edge) (third edge)))
									  result)
								    (format graph "}"))))))
		  
		  ((string= command "neighborhood-reasoning") (neighborhood-reasoning:neighborhood-reasoning (make-two-way-stream *standard-input* *standard-output*) calculi:*calculus* args))
								   
		  ((string= command "a-reasoning")
		   (a-reasoning:process-command *standard-output* calculi:*calculus* args))
		  (t (format *error-output* "Command '~a' is unknown!~%" command)
		     (print-usage)))))))))

(declaim (inline sfind))
(defun sfind (name list)
  (find name list :test #'string=)) 

(declaim (inline smember))
(defun smember (name list)
  (member name list :test #'string=))

(defun print-banner (stream)
  (format stream "~{;; ~a~%~};;~%;; SparQ ~a built using Lisp ~a~%;;~%"
	  '(""
	    "This is SparQ - SPAtial Reasoning done Qualitatively"
            "SparQ is free software, provided as is, with absolutely no warranty."
	    "(C) 2006-2009 Diedrich Wolter, SFB/TR 8"
            "See the file COPYING for details.")
          sparq:+sparq-version-name+ sparq:+built-info+))

#+SBCL
(defun accept (socket)
  "Like socket-accept, but retry on EAGAIN."
  (loop (handler-case
            (return (sb-bsd-sockets:socket-accept socket))
          (sb-bsd-sockets:interrupted-error ()))))

;; handler invoked when something goes truly wrong...
(defun sparq-quit (condition hook)
  (declare (ignore hook))
  (unless sparq:*debug*
    (if (typep condition 'simple-condition)
	(format t "~&--- abnormal exit (reason ~a) ---~%" (apply #'format (append (list nil (simple-condition-format-control condition))
										  (simple-condition-format-arguments condition))))
	(format t "~&--- abnormal exit (reason ~a) ---~%" (type-of condition)))
    (finish-output)
    (sb-ext:quit)))

(defun main ()
  (setf *debugger-hook* #'sparq-quit)
  (setf *random-state* (make-random-state t))
  (get-cpu-info)
  (multiple-value-bind (dummy error) 
      (progn ;ignore-errors
	(progn
	  (let* ((args #+SBCL (cdr (member "--end-toplevel-options" sb-ext:*posix-argv* :test #'string=)))
		 (error (catch 'error
			  ;; turn verbose mode on
			  (when (or (sfind "-v" args)
				    (sfind "--verbose" args))
			    (setq args (delete "--verbose" (delete "-v" args :test #'string=) :test #'string=)
				  *debug* t))

			  ;; turn timing mode on
			  (when (or (sfind "-t" args)
				    (sfind "--timing" args))
			    (setq args (delete "--timing" (delete "-t" args :test #'string=) :test #'string=)
				  *timing* t))

			  ;; set calculi directory
			  (when (or (sfind "-c" args) (sfind "--calculidir" args))
			    (let* ((calculi-arg (cdr (member-if #'(lambda (arg)
								    (or (string= "-c" arg)
									(string= "--calculidir" arg)))
								args)))
				   (cdirs (list "-c" "--calculidir" (car calculi-arg))) ; list of all calculi directories scanned plus args
				   (next-c-arg calculi-arg))
			      (loop while next-c-arg do
				   (setq next-c-arg (member-if #'(lambda (arg)
								   (or (string= "-c" arg)
								       (string= "--calculidir" arg)))
							       calculi-arg))
				   (when next-c-arg
				     (setq calculi-arg (cdr next-c-arg))
				     (push (car calculi-arg) cdirs)))
			      (let ((cdir (car calculi-arg)))
				(setf sparq::*root-pathname* (make-pathname :directory (list :relative cdir))))
				;; remove consumed args
				(setq args (delete "--calculidir" (delete "-c" args :test #'string=) :test #'string=))
				(dolist (cd cdirs)
				  (setq args (delete cd args)))))
			  
			  ;; go into interactive mode?
			  (cond ((or (sfind "-i" args)
				     (sfind "-d" args)
				     (sfind "--interactive" args)
				     (sfind "--daemon" args))
				 (let* ((tcp? (or (smember "-p" args)
						  (smember "--port" args)))
					(port (if tcp?
						  (read-from-string (cadr tcp?) nil nil))))
				   (calculi:load-calculus-registry)
				   (if (and (integerp port)
					    (< 127 port 65535))
				       (progn
					 (format *standard-output* "~%Awaiting incoming connection on TCP/IP port ~a..." port)
					 (finish-output *standard-output*)
					 (multiple-value-bind (dummy error?) 
					     (ignore-errors
					       (let ((tcp-stream #+OPENMCL (ccl:accept-connection
									    (ccl:make-socket :address-family :internet 
											     :type           :stream 
											     :connect        :passive
											     :local-port     port
											     :reuse-address  t))
								 #+SBCL (let ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
									  (sb-bsd-sockets:socket-bind socket #(127 0 0 1) port)
									  (sb-bsd-sockets:socket-listen socket 2)
									  (sb-bsd-sockets:socket-make-stream (accept socket) :input t :output t :element-type 'character))))
						 (when tcp-stream
						   (write-line "Connected!")
						   (finish-output)
						   (unwind-protect
							(progn
							  (print-banner tcp-stream)
							  (sparq-interactive tcp-stream))
						     (close tcp-stream)))))
					   (declare (ignore dummy))
					   (when error?
					     (format *error-output* "~%Error opening TCP socket for listening (~a)." error?)
					     (finish-output *error-output*))))
				       (if tcp?
					   (signal-error "Cannot use port specified as '~a'~%" port)
					   (progn
					     (print-banner *standard-output*)
					     (sparq-interactive (make-two-way-stream *standard-input* *standard-output*)))))))

				;; print usage?
				((or (sfind "-h" args)
				     (sfind "--help" args)
				     (null args))
				 (print-usage))
				
				(t (calculi:load-calculus-registry)
				   (sparq-single-computation (member-if-not #'(lambda (arg) (char= #\- (char arg 0))) args))))
			  nil)))
	    (when error
	      (format *error-output* "~%An error occured: ~a" error)))
	  (format *standard-output* "~%")
	  (finish-output *standard-output*)
	  (finish-output *error-output*)))
    (declare (ignore dummy))
    (when error (format *error-output* "~%An unhandled internal error occured - sorry. Error = ~a ~%" error)))
  (finish-output *standard-output*)
  (finish-output *error-output*)
  (cl-user::quit))
