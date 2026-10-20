@[expose] public section

open scoped Topology

universe u v

namespace CharacterModule

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A]

section Comparison

variable [CompactSpace A] [NonarchimedeanAddGroup A]

variable [T2Space A]

@[simp] theorem torsionEquivPontryaginOfDenseFG_symm_apply (D : AddSubgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A))
    (χ : Additive (PontryaginDual (Multiplicative A))) (a : A) :
    Additive.toMul (AddCircle.rationalToCircle
      (((torsionEquivPontryaginOfDenseFG D hfg hdense).symm χ).1 a)) =
      Additive.toMul χ (Multiplicative.ofAdd a) := by
  rw [← torsionEquivPontryaginOfDenseFG_apply D hfg hdense,
    (torsionEquivPontryaginOfDenseFG D hfg hdense).apply_symm_apply]

end Comparison
end CharacterModule
end
