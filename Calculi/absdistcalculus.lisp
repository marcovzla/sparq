;;; Absolute distance calculus
;;;

(def-calculus "Absolute distance calculus (absdistcalculus)"
  :arity :binary
  :basis-entity :2d-point
  :consistency :scenario-consistency
;  :qualifier (external-lib "TestLib.dylib" "test_compose")
  :qualifier #'(lambda (p1 p2)
		 (if (< (point-distance2 p1 p2) (expt calculi:*calculus-parameter* 2))
		     'close
		     'far))
  :converse-operation ((close close)
                       (far far))
  :identity-relation close
  :base-relations (close far)
  :composition-operation ((far close (close far))
                          (close far (close far))
                          (close close (close far))
                          (far far (close far))))

