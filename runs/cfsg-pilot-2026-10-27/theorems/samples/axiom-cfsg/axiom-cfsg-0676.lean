public section

open CFSG.Open

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Lemma216

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G S : Subgroup Γ}

namespace Hyp

variable [Finite Γ] (H : Hyp p A G S)

include H

theorem s0_le_W
    : s0 G S ≤ G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨kOf_le G (s0_le_kOf hx), ?_⟩
  refine (mem_sectionCentralizer_iff_of_le le_sup_right).mpr
    ⟨le_normalizer_fittingSubgroupOf _ hx, fun y hy => ?_⟩
  have h1 := (mem_s2_iff.mp (H.sup_le_s2 hy)).2 x hx
  rw [← commutatorElement_inv]
  exact inv_mem h1

end Hyp
end Lemma216
end CFSG.SignalizerFunctorTheorem.McBride.Near
end
