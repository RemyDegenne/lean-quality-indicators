public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

section Fac

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}
  (Mm : MatModel L₁ L₂ F d) {Y' Y : Submodule F (Fin d → F)}

theorem facAct_conj (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) (a : ↥P) (l : ↥L₁)
    (h : (a : MulAut U) * l * (a : MulAut U)⁻¹ ∈ L₁) :
    facAct Mm D hP hP' a * natAut Mm l * (facAct Mm D hP hP' a)⁻¹ = natAut Mm ⟨_, h⟩ := by
  rw [mul_inv_eq_iff_eq_mul]
  refine MulEquiv.ext fun x => ?_
  set w := rank1 Mm (Multiplicative.toAdd x) D.y
  have key : ((a : MulAut U) * l * (a : MulAut U)⁻¹) ((a : MulAut U) w) =
      (a : MulAut U) ((l : MulAut U) w) := by
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  rw [MulAut.mul_apply, MulAut.mul_apply, facAct_eq_facProj, facAct_eq_facProj,
    natAut_apply Mm l x, toAdd_ofAdd, rank1_mulVec, ← key]
  exact facProj_act Mm D ⟨_, h⟩ _

end Fac
end CFSG.Quasithin.SmithD37
end
