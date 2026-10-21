namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

open Filter

namespace Thorp.Young

open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

lemma extensions_nonempty : Nonempty (Extensions A) := by
  let h : A ≃ LinearExtension A := Equiv.refl A
  let : Fintype (LinearExtension A) := Fintype.ofEquiv A h
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension A) (Fintype.card_congr h.symm)).symm
  refine ⟨⟨h.trans e.toEquiv, ?_⟩⟩
  exact e.strictMono.comp
    (toLinearExtension.monotone.strictMono_of_injective fun _ _ hh => hh)

end Thorp.Young
end
end OAI
