public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

section Helpers

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {Bs L : Subgroup G} {x : G}

lemma qtwoDB19_ggPermSU_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1 := by
  rw [show ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) =
      (σ⁻¹).permMatrix F0 from rfl, Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.symm_apply_eq σ) rfl rfl

end Helpers
end CFSG.StandardType.QTwo
end
