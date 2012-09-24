
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin BX Predicates

;;;;; hard-coding these for now, rather than defining them in !D syntax

(declare-fun docDomain (DVal DVal) Bool)
(declare-fun eltDoc (DVal DVal) Bool)
(declare-fun eltParentChild (DVal DVal) Bool)
;;; (declare-fun eltAncestorDesc (DVal DVal) Bool)
(declare-fun eltTagName (DVal DVal) Bool)
(declare-fun eltAttr (DVal DVal DVal) Bool)
(declare-fun eltTextValue (DVal DVal) Bool)
(declare-fun flowsFromTo (DVal DVal) Bool)
;;; (declare-fun canAppend (DVal) Bool)
(declare-fun canAppend (DVal DVal) Bool)
(declare-fun canEdit (DVal) Bool)
(declare-fun canReadAttr (DVal DVal) Bool)
(declare-fun canWriteAttr (DVal DVal DVal) Bool)
(declare-fun canReadValue (DVal) Bool)
(declare-fun canFlowTo (DVal DVal) Bool)
(declare-fun canReadSelection (DVal) Bool)
(declare-fun canStyle (DVal) Bool)
(declare-fun selection (DVal) Bool)
(declare-fun canReadFile (DVal) Bool)
(declare-fun canRequest (DVal DVal) Bool)
(declare-fun canReadHistory (DVal) Bool)
(declare-fun eltStyle (DVal DVal) Bool)
(declare-fun urlHost (DVal DVal) Bool)
(declare-fun urlScheme (DVal DVal) Bool)
(declare-fun urlPath (DVal DVal) Bool)
(declare-fun parseUrl (DVal DVal) Bool)

;;;;; End BX Predicates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

