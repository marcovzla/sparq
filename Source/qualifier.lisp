;;; This file is part of SparQ, a toolbox for qualitative spatial reasoning.
;;; Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Diedrich Wolter, Project R3-[Q-Shape]
;;; See http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

;;; SparQ is free software and has been released under the terms of the GNU
;;; General Public License version 3 or later. You should have received a
;;; copy of the GNU General Public License along with this program. If not,
;;; see <http://www.gnu.org/licenses/>.
;;;

;;;
;;; SparQ relation qualification
;;;

;; Change history (most recent first):
;; 2006-10-26 DW  initial version for SparQ V0.7

(defpackage :qualifier
  (:use :common-lisp :sparq :calculi)
  (:export :qualify :parse-entity))

(in-package :qualifier)

(defgeneric parse-entity (entity it)
            (declare (ignore entity it)))

(defmethod parse-entity ((what (eql :1d-point)) it)
  (if (or (nthcdr 2 it)
          (not (symbolp (car it)))
          (not (realp (second it))))
    (signal-error "Specification '~a' is not of the required type 1d point, i.e. (identifier x)~%" it)
    it))

(defmethod parse-entity ((what (eql :2d-point)) it)
  (if (or (nthcdr 3 it)
          (not (symbolp (car it)))
          (not (realp (second it)))
          (not (realp (third it))))
    (signal-error "Specification '~a' is not of the required type 2d point, i.e. (identifier x y)~%" it)
    it))

(defmethod parse-entity ((what (eql :3d-point)) it)
  (if (or (nthcdr 4 it)
          (not (symbolp (car it)))
          (not (realp (second it)))
          (not (realp (third it))))
    (not (realp (fourth it))))
  (signal-error "Specification '~a' is not of the required type 3d point, i.e. (identifier x y z)~%" it)
  it)

(defmethod parse-entity ((what (eql :interval)) it)
  (if (or (nthcdr 3 it)
          (not (symbolp (car it)))
          (not (realp (second it)))
          (not (realp (third it))))
    (signal-error "Specification '~a' is not of the required type point, i.e. (identifier a b)~%" it)
    it))

(defmethod parse-entity ((what (eql :dipole)) it)
  (if (or (nthcdr 5 it)
          (not (symbolp (car it)))
          (not (realp (second it)))
          (not (realp (third it)))
          (not (realp (fourth it)))
          (not (realp (fifth it))))
    (signal-error "Specification '~a' is not of the required type dipole, i.e. (identifier start-x start-y end-x end-y)~%" it)
    it))

(defmethod parse-entity ((what (eql :2d-oriented-point)) it)
  (if (or (nthcdr 5 it)
          (not (symbolp (car it)))
          (not (realp (second it)))
          (not (realp (third it)))
          (not (realp (fourth it)))
          (not (realp (fifth it))))
    (signal-error "Specification '~a' is not of the required type dipole, i.e. (identifier start-x start-y dir-x dir-y)~%" it)
    it))

;; funtion to generate all permutations of a list, found at:
;; http://stackoverflow.com/questions/2087693/how-can-i-get-all-possible-permutations-of-a-list-with-common-lisp/8448611#8448611
(defun all-permutations (lst &optional (remain lst))
  (cond ((null remain) nil)
        ((null (rest lst)) (list lst))
        (t (append
             (mapcar (lambda (l) (cons (first lst) l))
                     (all-permutations (rest lst)))
             (all-permutations (append (rest lst) (list (first lst))) (rest remain))))))

;; Dummy declaration to make SBCL happy
(defgeneric qualify-scenario (arity option calculus scenario)
            (declare (ignore arity option calculus scenario)))

(defmethod qualify-scenario ((arity (eql :binary)) (option (eql :first2all)) calculus scenario)
  (let ((o1 (first scenario))
        (b (calculi:calculus-basis-entity calculus))
        (qfun (calculi::calculus-qualifier calculus)))
    (mapc #'(lambda (x)
              (parse-entity b x))
          scenario) ; Error checking
    (mapcar #'(lambda (o2)
                (list (car o1) (funcall qfun (cdr o1) (cdr o2)) (car o2)))
            (rest scenario))))

(defmethod qualify-scenario ((arity (eql :binary)) (option (eql :all)) calculus scenario)
  (let ((qfun (calculi::calculus-qualifier calculus))
        scene)
    (do ((o1s scenario (cdr o1s)))
      ((null o1s))
      (do ((o2s (cdr o1s) (cdr o2s)))
        ((null o2s))
        (push (list (caar o1s) (funcall qfun (cdar o1s) (cdar o2s)) (caar o2s))
              scene)))
    (nreverse scene)))

(defmethod qualify-scenario ((arity (eql :binary)) (option (eql :all2all)) calculus scenario)
  (let ((qfun (calculi::calculus-qualifier calculus))
        scene)
    (do ((o1s scenario (cdr o1s)))
      ((null o1s))
      (do ((o2s (cdr o1s) (cdr o2s)))
        ((null o2s))
        (dolist (tuple (all-permutations (list o1s o2s)))
          (push (list (caar (first tuple))
                      (funcall qfun (cdar (first tuple)) (cdar (second tuple)))
                      (caar (second tuple)))
                scene))))
    (nreverse scene)))

(defmethod qualify-scenario ((arity (eql :ternary)) (option (eql :first2all)) calculus scenario)
  (let ((o1 (first scenario))
        (o2 (second scenario))
        (qfun (calculi::calculus-qualifier calculus)))
    (mapcar #'(lambda (o3)
                (list (car o1) (car o2) (funcall qfun (cdr o1) (cdr o2) (cdr o3)) (car o3)))
            (cddr scenario))))

(defmethod qualify-scenario ((arity (eql :ternary)) (option (eql :all)) calculus scenario)
  (let ((qfun (calculi::calculus-qualifier calculus))
        scene)
    (do ((o1s scenario (cdr o1s)))
      ((null o1s))
      (do ((o2s (cdr o1s) (cdr o2s)))
        ((null o2s))
        (do ((o3s (cdr o2s) (cdr o3s)))
          ((null o3s))
          (push (list (caar o1s) (caar o2s) (funcall qfun (cdar o1s) (cdar o2s) (cdar o3s)) (caar o3s))
                scene))))
    (nreverse scene)))

(defmethod qualify-scenario ((arity (eql :ternary)) (option (eql :all2all)) calculus scenario)
  (let ((qfun (calculi::calculus-qualifier calculus))
        scene)
    (do ((o1s scenario (cdr o1s)))
      ((null o1s))
      (do ((o2s (cdr o1s) (cdr o2s)))
        ((null o2s))
        (do ((o3s (cdr o2s) (cdr o3s)))
          ((null o3s))
          (dolist (triple (all-permutations (list o1s o2s o3s)))
            (push (list (caar (first triple))
                        (caar (second triple))
                        (funcall qfun (cdar (first triple)) (cdar (second triple)) (cdar (third triple)))
                        (caar (third triple)))
                  scene)))))
    (nreverse scene)))

(defun qualify (calculus cmd-stream stream state)
  (declare (ignore state))
  (let ((option (save-read cmd-stream)))
    (unless (functionp (calculi::calculus-qualifier calculus))
      (signal-error "No qualifier specified for calculus ~a!~%" (calculi:calculus-name calculus)))
    (cond ((eq option 'cl-user::all) (setq option :all))
          ((eq option 'cl-user::first2all) (setq option :first2all))
          ((eq option 'cl-user::all2all) (setq option :all2all))
          (t (signal-error "Option '~a' not recognized.~%" option)))
    (multiple-value-bind (descr error) (values (let ((scenario (ignore-errors (read cmd-stream))))
                                                 (mapc #'(lambda (x)
                                                           (parse-entity (calculi:calculus-basis-entity calculus) x))
                                                       scenario) ; Error checking
                                                 (let ((symbols (mapcar #'first scenario)))
                                                   (setq symbols (delete-duplicates (delete-if #'null (mapcar #'(lambda (item) (if (< 1 (count item symbols)) item))
                                                                                                              symbols))))
                                                   (when symbols
                                                     (signal-error "Multiple definition of symbol~P ~{~a ~} !~%" (length symbols) symbols)))
                                                 (qualify-scenario (calculi:calculus-arity calculus) option calculus scenario)))
      (if error
        (signal-error "Error in qualification process.~%")
        (progn
          ;(when state
          ;  (setf (sparq::sparq-state-last-result state) descr))
          (if descr
            (progn
              (format stream "(")
              (if (eq (calculi:calculus-arity calculus) :binary)
                (dolist (orel descr)
                  (format stream "(~a ~(~a~) ~a) " (first orel) (let ((tmp (second orel)))
                                                                  (if (and (listp tmp) (null (cdr tmp)))
                                                                    (car tmp)
                                                                    tmp))
                          (third orel)))
                (dolist (orel descr)
                  (format stream "(~a ~a ~(~a~) ~a) " (first orel) (second orel) (let ((tmp (third orel)))
                                                                                   (if (and (listp tmp) (null (cdr tmp)))
                                                                                     (car tmp)
                                                                                     tmp))
                          (fourth orel))))
              (format stream ")~%"))
            (write-line "()" stream))
          descr)))))


#|
(defun qualify (calculus cmd-stream stream state)
  (let (option
         scenario
         (qfun (calculi::calculus-qualifier calculus)))
    (unless (functionp qfun)
      (signal-error "No qualifier specified for calculus ~a!~%" (calculi:calculus-name calculus)))
    (multiple-value-bind (dummy error)
      (ignore-errors
        (setq option (read cmd-stream nil nil)))
      (declare (ignore dummy))
      (if error
        (signal-error "An reader error occured (e.g. unmatched paranthesis).~%")
        (progn
          (cond ((eq option 'cl-user::all) (setq option :all))
                ((eq option 'cl-user::first2all) (setq option :first2all))
                (t (setq option nil)))
          (unless option
            (signal-error "Option '~a' not recognized.~%" option))
          (multiple-value-bind (descr error) (ignore-errors (funcall qfun cmd-stream option))
            (if error
              (signal-error "Error in qualification process.~%")
              (progn
                (setf (sparq::sparq-state-last-result state) descr)
                (if descr
                  (progn
                    (format stream "(")
                    (if (eq (calculi:calculus-arity calculus) :binary)
                      (dolist (orel descr)
                        (format stream "(~a ~(~a~) ~a) " (first orel) (second orel) (third orel)))
                      (dolist (orel descr)
                        (format stream "(~a ~a ~(~a~) ~a) " (first orel) (second orel) (third orel) (fourth orel))))
                    (format stream ")~%"))
                  (write-line "()" stream))))))))))
|#

;;;
;;; Parsing functions for the qualifier
;;;

(in-package :cl-user)

(defun point-distance2 (p1 p2)
  (+ (expt (- (first p1) (first p2)) 2)
     (expt (- (second p1) (second p2)) 2)))

(defun dipole-point-relation (d p)
  (destructuring-bind (sax say eax eay) d
    (destructuring-bind (px py) p
      (cond ((and (= sax eax px)
                  (= say eay py)) 'tri)
            ((and (= sax eax)
                  (= say eay)) 'dou)
            ((and (= sax px)
                  (= say py)) 's)
            ((and (= eax px)
                  (= eay py)) 'e)
            (t (let* ((dax (- eax sax))
                      (day (- eay say))
                      (sbrx (- px sax))
                      (sbry (- py say))
                      (x (+ (* sbrx day)
                            (* sbry (- dax)))))
                 (cond ((> 0 x) 'l)
                       ((< 0 x) 'r)
                       ((= x 0) (if (> 0 (+ (* (- px eax) dax) (* (- py eay) day)))
                                  (if (< 0 (+ (* (- px sax) dax) (* (- py say) day)))
                                    'i
                                    'b)
                                  'f)))))))))
