;;;
;;; QTC-C22: Qualitative Trajectory Calculus DoubleCross 2D Level 2 with 243 base relations
;;;

(def-calculus "QTC-C22: Qualitative Trajectory Calculus DoubleCross 2D Level 2 with 243 base relations"
  :arity :binary
  :parametric? nil
  ;;:qualifier (external-lib "libqtc.dylib" "qualify_qtc_c22")
  :basis-entity :dipole ;; 5-tuple with two dipoles, and relative velocity (relative angle left out)
  :base-relations #'(lambda ()  ;; Function to compute the base relations 5 times {+,0,-}
		      (let ((rels nil))
			(dolist (z1 '(- O +))
			  (dolist (z2 '(- O +))
			    (dolist (z3 '(- O +))
			      (dolist (z4 '(- O +))
				(dolist (z5 '(- O +))
				  ;;(dolist (z6 '(- O +))
				  ;;(push (intern (format nil "~a~a~a~a~a~a" z1 z2 z3 z4 z5 z6)) rels)))))))
				  (push (intern (format nil "~a~a~a~a~a" z1 z2 z3 z4 z5)) rels))))))
			(nreverse rels)))
  :identity-relation OOOOO
  :converse-operation (:external-lib "libqtc.dylib" "qtc_c22_converse")
  :composition-operation (:external-lib "libqtc.dylib" "qtc_c22_composition")
  
)


