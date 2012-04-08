;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;; Basic definitions and main loader of SparQ
;;; 
;;; This file contains the definition of the package sparq
;;; that contains some standard utility functions used throughout the
;;; rest of the code. Furthermore, compilation of sparq into an executable
;;; binary is defined. The main functions are:
;;; - signal-error          to signal errors to the user (e.g. you didn't supply the right arguments)
;;; - make-local-pathname   constructs a pathname that points into the SparQ directory structure
;;; - load/compile          loads (and compiles if necessary) a lisp file
;;; - ofuncs                ofuncs are objects that represent source code and compiled function such that
;;;                         instance-specific optimmization can be performed by recompiling optimized
;;;                         source code
;;; - make-sparq            constructs the SparQ binary and shell script to invoke it


;; Change history (most recent first):
;; 2008-05-29 DW   added cpu-info
;; 2006-10-27 DW   after 0.6 branch is split of we're heading towards 0.7: new calculi & relation representation
;; 2006-10-24 DW   changed ofuncs to be a class now so we can have post-init functions that derive the 
;;                 callable from its code such we can implement make-load-form

#+SBCL (require 'SB-BSD-SOCKETS)
;(require :sb-sprof)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (declaim (sb-ext:muffle-conditions sb-ext:compiler-note))
  (declaim (sb-ext:muffle-conditions sb-ext:code-deletion-note)))


(defpackage :sparq
  (:use :common-lisp)
  (:export :*debug*  :*timing* :save-read :signal-error :make-local-pathname :load/compile :*sparq-readtable*
	   :ofunc-macro-code :ofunc-prefetch-data :time-string :get-cpu-info :*num-processors* :*processor-speed*
	   :+nothing+ :make-sparq :main :+sparq-version-name+ :+built-info+ :make-ofunc :?curry :with-timing :report-time))

(in-package :sparq)

(defparameter *root-pathname* *load-pathname*
  "The root directory of sparQ.")

(defparameter *sparq-readtable* (let ((rt (copy-readtable nil)))
				  (setf (readtable-case rt) :preserve)
				  rt)
  "Readtable for parsing input")

;; Debug flag set by the "-v" command line option
(defparameter *debug* nil "Debug flag")

;; Timing flag set by the "-t" command line option
(defparameter *timing* nil "Timing flag")

;; Handling of program errors to be reported to the user
(defmacro signal-error (control-string &rest args)
;  `(error ,(concatenate 'string control-string "~&") ,@args))
  `(throw 'error (format nil ,(concatenate 'string control-string "~&") ,@args)))

(defun save-read (stream)
  "A read that will use SparQ's error signaling mechanism when something goes wrong"
  (multiple-value-bind (obj error) (ignore-errors (read stream))
    (if error
	(signal-error "Reader error (~a)" error)
	obj)))

;; SBCL-proof defconstant
;; -> see SBCL manual for discussion on the use of defconstant
(defmacro define-constant (name value)
  `(defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)))

;; A constant that is not equal to anything but itself allows distinguishing parsing nil and failing to parse
(define-constant +nothing+ (gensym))

(define-constant +sparq-version-name+ "V0.7.4")

(define-constant +built-info+ (multiple-value-bind (sec min std day mon year) (get-decoded-time)
				(format nil "~a (~a) on ~a-~2,'0d-~2,'0d ~a:~2,'0d.~2,'0d" (lisp-implementation-type) (machine-type) year mon day std min sec)))

;; returns current time as string
(defun time-string ()
  (multiple-value-bind (sec min std day mon year) (get-decoded-time)
    (format nil "~a-~2,'0d-~2,'0d ~a:~2,'0d.~2,'0d"year mon day std min sec)))


;; Converts a name (string) and type (string) into a valid
;; pathname that points into sparQ source directory
(defun make-local-pathname (dir name &optional type)
  (declare (special *root-pathname*))
  (if type
      (make-pathname :host      (pathname-host *root-pathname*) 
		     :directory (append (butlast (pathname-directory *root-pathname*)) (list dir))
		     :device    (pathname-device *root-pathname*)
		     :name      name
		     :type      type)
      (make-pathname :host      (pathname-host *root-pathname*) 
		     :directory (append (butlast (pathname-directory *root-pathname*)) (list dir))
		     :device    (pathname-device *root-pathname*)
		     :name      name)))

;; Loads a file (string) from the sparQ source directory
;; The file is compiled before loading, but only if no
;; compiled file already exists which is not older than
;; the source file
(defun load/compile (dir file &key (compile-always nil) (verbose nil) (pathname nil))
  (let* ((source (or pathname (make-local-pathname dir file "lisp")))
         (fasl (merge-pathnames (make-pathname :type "fasl") source)))
    (unless (probe-file source)
      (error "Error, file '~s' not found!" file))
    (when (or compile-always
	      (not (probe-file fasl))
              (< (file-write-date fasl)
                 (file-write-date source)))
      (if verbose
	  (progn
	    (format t "~%;; Compiling \"~a.~a\" -> \"~a.~a\"" (pathname-name source) (pathname-type source) (pathname-name fasl) (pathname-type fasl))
	    (compile-file source :output-file (make-pathname :directory (list :relative) :name file :type (pathname-type fasl)) :verbose verbose :print *error-output*))
	  (with-output-to-string (dummy)
	    (locally (declare (sb-ext:muffle-conditions sb-ext:compiler-note style-warning))
	      (handler-bind ((style-warning #'muffle-warning))
		(compile-file source :output-file (make-pathname :directory (list :relative) :name file :type (pathname-type fasl)) :verbose verbose :print dummy))))))
    (if verbose
	(progn
	  (format t "~%;; \"~a.~a\" ~ashould exist, loading...~%"
		  (pathname-name fasl)
		  (pathname-type fasl)
		  (subseq "                                            " (length (pathname-name fasl))))
	  (load fasl))
	(handler-bind ((style-warning #'muffle-warning))
	  (load fasl)))))

(defvar *num-processors* 1)
(defvar *processor-speed* 2000000000)

;; returns number of cpus on system and their clock frequency
(defun get-cpu-info ()
  (declare (special *num-processors* *processor-speed*))
  (ignore-errors ;; the code might fail but we don't really care...
    #+BSD (let* ((sys (with-output-to-string (out)
			(sb-ext:run-program  "/usr/sbin/sysctl" '("hw.cpufrequency" "hw.ncpu") :if-error-exists :ignore :output out)))
		 (lbreak (position #\Newline sys)))
	    
	    (setq *num-processors* (read-from-string sys nil nil :start (+ lbreak 10))
		  *processor-speed* (read-from-string sys nil nil :start 17)))
    #+LINUX (let ((sys (make-string-input-stream (with-output-to-string (out)
						   (sb-ext:run-program "/bin/cat" '("/proc/cpuinfo") :if-error-exists :ignore :output out))))
		  (nprocs 0)
		  (clk 0))
	      (loop while (listen sys) do
		   (let* ((line (read-line sys nil nil))
			  (l (length line)))
		     (if (and (<= 9 l) ; make sure 'end2' is valid
			      (string= "processor" line :end2 9))
			 (incf nprocs)
			 (if (and (<= 7 l)
				  (string= "cpu MHz" line :end2 7))
			     (incf clk (read-from-string line nil nil :start (1+ (position #\: line))))))))
	      (when (< 0 nprocs)
		(setq *num-processors* nprocs 
		      *processor-speed* (round (* 1e6 (/ clk nprocs))))))))

;;
;; Loader that loads (and compiles, if necessary) all SparQ source files
;;
;; args can be used to pass on keyword args to the load/compile function (see above)
(defun load-sparq (&key (compile-always nil) (verbose nil))
  (let ((files-to-load '("ofuncs" "relations" "rb-trees-SE" "calculi" "polynomials" "numeric-optimizer" "poly-model" "groebner" "poly-solver" "poly-solver-patterns" 
			 "compute-relation" "constraint-networks" "binary-constraint-reasoning" "ternary-constraint-reasoning" "constraint-reasoning"
			 "qualifier" "algebraic-reasoning" "neighborhood-reasoning" "quantifier" "interface" "main"))
	errors)
    (dolist (file files-to-load)
      (multiple-value-bind (dummy error) (ignore-errors (load/compile "Source" file :compile-always compile-always :verbose verbose))
	(declare (ignore dummy))
	(when error
	    (format *error-output* "~%An error occured while loading the file '~a',   Error: ~a" file error)
	      (push (cons file error) errors))))
    (when errors
      (format *error-output* "~%~%~%~a ERROR(S) OCCURED DURING COMPILATION/LOADING:" (length errors)) 
      (format *error-output* "~%Please send this error message and information about the Lisp system in use to qshape@informatik.uni-bremen.de.")
      (format *error-output* "~%Lisp System: ~a, version: ~a" (lisp-implementation-type) (lisp-implementation-version))     
      (let ((filler "                                                "))
        (dolist (file/error (nreverse errors))
          (format *error-output* "~%File: '~a' ~aError: ~a" (car file/error) (subseq filler (length (format nil "~a" (car file/error)))) (cdr file/error)))))))


;; 
;; Utility function for compiling Sparq as executable binary
;; ATTENTION: ONCE CALLED, THE CURRENTLY ACTIVE LISP WILL TERMINATE!!
;;;
#+SBCL (defun make-sparq ()
  (load-sparq)
  (setf *print-pretty* nil)
					;(setf *break-on-signals* t)
  ;; Generate the start script
  (with-open-file (start-script "SparQ" :direction :output :if-exists :supersede)
    (write-line "#!/bin/sh" start-script)
    (write-line "./SparQ.bin --noinform --end-runtime-options --no-sysinit --no-userinit --end-toplevel-options $*" start-script))
  ;; Save binary and exit
  (sb-ext:save-lisp-and-die "SparQ.bin" :toplevel #'(lambda () (funcall 'main)) :executable t))

;;;
;;; Utilities
;;; (once there are too many we'll set up a separate file for them)
;;;

;; universal curry 
;; example: (?curry (find ?x (cons 2 ?lst))) ---> (lambda (?x ?y) (find ?x (cons 2 ?lst)))
(defmacro ?curry (call)
  (labels ((lambda-args (form)
	     (if (consp form)
		 (mapcan #'lambda-args form)
		 (if (and (symbolp form)
			  (char= #\? (char (symbol-name form) 0)))
		     (list form)
		     (if (eq form '?curry)
			 (error "in macroexpansion of ?curry: nestings of ?curry not allowed"))))))
    `(lambda ,(lambda-args call)
       ,call)))

(defvar *times* nil)
(declaim (inline report-time))
(defun report-time (tag)
  (declare (optimize (speed 3) (safety 0)))
  (push (cons (get-internal-real-time) tag) *times*))

(defmacro with-timing (stream &body body)
  (let ((result (gensym)))
    `(progn (setf *times* (list (get-internal-real-time)))
	    (let ((,result (progn ,@body)))
	      (setq *times* (nreverse *times*))
	      (let* ((now (pop *times*))
		     (last-time now))
		(when *timing*
		  (format ,stream "~&;; TIME [sec]:")
		  (mapc #'(lambda (ti)
			    (format ,stream "~&;; ~5,2f (subtotal ~5,2f) ~a"
				    (* 1e-3 (- (car ti) last-time))
				    (* 1e-3 (- (car ti) now))
				    (cdr ti))
			    (setq last-time (car ti)))
			*times*)
		  (format ,stream "~%;; TOTAL:          ~,2f~%" (* 1e-3 (- last-time now))))
		,result)))))
