@[expose] public section

noncomputable section

attribute [local implicit_reducible] 𝓛ZF

variable {M N M₀ : Type _} [ZFStructure M] [ZFStructure N] [ZFStructure M₀]

open Subtype in
attribute [instance low] instLE instLT instLawfulOrderLT instMin instMax instReflLE instAntisymmLE
  instTotalLE Subtype.instTransLE instMinEqOr instLawfulOrderMin instMaxEqOr instLawfulOrderMax
  instIsPreorder instIsLinearPreorder instIsPartialOrder instIsLinearOrder preorder partialOrder
  decidableLE decidableLT

open Order ZFSet Function Cardinal

prefix:max "↓" => toV

prefix:max "⇓" => toZFSet

open SetTheory

variable [hM : IsVonNeumann M] [hN : IsVonNeumann N] [hM₀ : IsVonNeumannWithOmega M₀]

macro "split_vonNeumann" h:ident : tactic => do
  let μ := Lean.mkIdent `μ
  let hμ := Lean.mkIdent `hμ
  `(tactic | (rcases $h:ident with ⟨$μ, $hμ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; have _ := Fact.mk $hμ))

macro "split_vonNeumann_omega" h:ident : tactic => do
  let μ := Lean.mkIdent `μ
  let hμ := Lean.mkIdent `hμ
  let omega_lt_μ := Lean.mkIdent `omega_lt_μ
  `(tactic | (rcases $h:ident with ⟨$μ, $hμ, $omega_lt_μ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; have _ := Fact.mk $hμ))

namespace SetTheory

lemma le_def {x y : M} : x ≤ y ↔ x ⊆ y := Iff.rfl

end SetTheory
end
end
