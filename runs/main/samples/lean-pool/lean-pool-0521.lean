@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language} {μ : Type*} [Semiformula.Operator.Eq L]

notation "𝐄𝐐" => eqAxiom

namespace ModelOfSatEq

variable {T : Theory L} [𝐄𝐐 wkn T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)

lemma models : ModelOfSatEq sat ⊧ₘ* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat :=
    Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

end ModelOfSatEq
end FirstOrder
end LO
end
