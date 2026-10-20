namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open

open scoped Quaternion

noncomputable section

namespace CerednikDrinfeld

namespace QM

namespace SpecialOfFEC

p2m_open

section Lie

variable {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] (X : FormalODModule q B)

abbrev sc : B →+* Matrix (Fin 2) (Fin 2) B := algebraMap B (Matrix (Fin 2) (Fin 2) B)

end Lie
end SpecialOfFEC
end QM
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial
