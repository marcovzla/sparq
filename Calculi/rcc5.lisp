;;; 
;;; Region Connection Calculus with 5 base relations (RCC5)
;;;

(def-calculus "Region Connection Calculus with 5 base relations (RCC5)"
  :arity :binary
  :parametric? nil
  :consistency :scenario-consistency
  :identity-relation eq
  :converse-operation ((dr  dr)
		       (po  po)
		       (pp  ppi)
		       (ppi pp)
		       (eq  eq))  
  :base-relations (eq dr po pp ppi)
  :composition-operation (
			  (eq eq    eq)
			  (eq dr    dr)
			  (eq po    po)
			  (eq pp    pp)
			  (eq ppi   ppi)

			  (dr eq    dr)
			  (dr dr    (dr po pp ppi eq ))
			  (dr po    (dr po pp ))
			  (dr pp    (dr po pp ))
			  (dr ppi   ppi)

			  (po eq    po)
			  (po dr    (dr po ppi ))
			  (po po    (eq dr po pp ppi ))
			  (po pp    (po pp ))
			  (po ppi   (dr po ppi ))
 
			  (pp eq    pp )
			  (pp dr    dr )
			  (pp po    (dr po pp ))
			  (pp pp    pp )
			  (pp ppi  (eq dr po pp ppi))

			  (ppi eq   ppi)
			  (ppi dr   (dr po ppi ))
			  (ppi po   (po ppi ))
			  (ppi pp   (eq po pp ppi))
			  (ppi ppi  ppi )

                         ))




