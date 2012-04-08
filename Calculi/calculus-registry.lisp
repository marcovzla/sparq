
;;; SparQ calculi registry
;;;
;;; Specify calculi names and corresponding files as list ("name" "alias-name-1" "alias-name-2" ... "file-name")
;;; Observe that calculi names need to provide a unique prefix - any characters appending the supplied name
;;; will be interpreted as parameters of the calculus, e.g. "OPRA-2" is interpreted as calculus "OPRA-" and
;;; "2" is interpreted as parameter which in the case of the opra calculus family specifies the granularity

(; calculus-name(s)          file-name (without extension !!)
 ; ----------------------------------------------------------
 ("cardir"                   "cardir")
 ("dra-24" "dipole-coarse"   "dipole")
 ("pc" "point-calculus" "pa" "point-algebra"    "point-calculus")
 ("double-cross" "DCC"       "double-cross")
 ("alternative-double-cross" "adcc" "double-cross2")
 ("single-cross" "SCC"       "single-cross")
 ("OPRA-"                    "opra-calculus")
 ("absdistcalculus-"         "absdistcalculus") 
 ("reldistcalculus"          "reldistcalculus")
 ("flipflop" "ffc" "ff"      "flipflop")
 ("rcc-8"                    "rcc8")
 ("rcc-5"                    "rcc5")
 ("allen" "aia" "ia"         "allen")
 ("qtc-b11"                  "qtc-b11")
 ("qtc-b12"                  "qtc-b12")
 ("qtc-c22"                  "qtc-c22")
 ("qtc-c21"                  "qtc-c21")
 ("qtc-b22"                  "qtc-b22")
 ("qtc-b21"                  "qtc-b21")
 ("dep" "depcalc"            "dependency")
 ("geomori" "ori" "align"    "geometric-orientation")
)
 
 