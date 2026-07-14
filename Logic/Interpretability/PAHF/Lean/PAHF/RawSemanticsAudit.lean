import PAHF.RawSemantics

/-! Focused assumption audit for arbitrary-HF raw PA semantics. -/

open SetTheory

#check @AckermannHF.PAInHF.fofamPAPreModel
#check @AckermannHF.PAInHF.fofamPATermEval_graph_iff
#check @AckermannHF.PAInHF.formulaAt_iff_fofamPAFormulaSat
#check @AckermannHF.PAInHF.fofam_PA_Ax_s_valid
#check @AckermannHF.PAInHF.fofam_PA_BProv_soundness

#print axioms AckermannHF.PAInHF.fofamPATermEval_graph_iff
#print axioms AckermannHF.PAInHF.formulaAt_iff_fofamPAFormulaSat
#print axioms AckermannHF.PAInHF.fofam_PA_Ax_s_valid
#print axioms AckermannHF.PAInHF.fofam_PA_BProv_soundness
