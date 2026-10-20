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

prefix:max "𝓟 " => powerset

@[realize] lemma insert.eu (x y : M) : IsSet {z | z = x ∨ z ∈ y} := by
  rw [isSet_iff]
  split_vonNeumann hM
  · refine ⟨⟨{x.1} ∪ y.1, mem_vonNeumann_union (mem_vonNeumann_singleton hμ x.2) y.2⟩, ?_⟩
    simp only [toZFSet_simps]
    simp
  · revert x y
    simpa only [toZFSet_simps] using fun x y => ⟨{x} ∪ y, by simp⟩

end SetTheory
end
end
