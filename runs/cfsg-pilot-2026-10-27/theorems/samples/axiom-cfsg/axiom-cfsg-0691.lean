public section

open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type*} [Group Γ]

theorem isPGroup_zpowers {p : ℕ} {b : Γ} (hbp : b ^ p = 1) :
    IsPGroup p (Subgroup.zpowers b) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  have : (g : Γ) ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  simpa using this

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux
end
