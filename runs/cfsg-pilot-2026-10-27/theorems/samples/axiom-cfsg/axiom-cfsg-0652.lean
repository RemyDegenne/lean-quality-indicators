public noncomputable section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

open CFSG.LieType.Ree.ReeTag

open scoped Pointwise

section Main

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

variable {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)

include hw₀

theorem coe_smallReeInvCentralizer
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (smallReeInvCentralizer a K : Set (ModGL G2.tag K)) =
      smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) ∪
        smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
          {canonicalRep (coxeterSystem G2.tag) K w₀} * smallReeMidX a K := by
  set n := canonicalRep (coxeterSystem G2.tag) K w₀
  ext g
  constructor
  · intro hg
    obtain ⟨hgΓ, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgt := Subgroup.mem_centralizer_singleton_iff.1 hgC
    have hfix : smallReeH a K (-1) * g * (smallReeH a K (-1))⁻¹ = g := by
      rw [← hgt, mul_inv_cancel_right]
    rcases reeGamma_G2_cases hw₀ hgΓ with ⟨u, hu, h, hh, rfl⟩ | ⟨-, u, hu, h, hh, v, hv, rfl⟩
    · left
      rw [smallReeH_conj_mul hK hh] at hfix
      exact ⟨u, mem_smallReeMidX_of_conj_eq hK hu (mul_right_cancel hfix), h, hh, rfl⟩
    · right
      rw [smallReeH_conj_bigCell hw₀ hK hh] at hfix
      obtain ⟨e1, -, e3⟩ := eq_of_mul_canonicalRep_mul_eq hw₀ (smallReeH_conj_mem hK hu)
        hu hh hh (smallReeH_conj_mem hK hv) hv hfix
      exact ⟨u * h * n, ⟨u * h, ⟨u, mem_smallReeMidX_of_conj_eq hK hu e1, h, hh, rfl⟩, n, rfl,
        rfl⟩, v, mem_smallReeMidX_of_conj_eq hK hv e3, rfl⟩
  · rintro (⟨u, hu, h, hh, rfl⟩ | ⟨_, ⟨_, ⟨u, hu, h, hh, rfl⟩, _, rfl, rfl⟩, v, hv, rfl⟩)
    · exact mul_mem (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hu)
        (mem_smallReeInvCentralizer_of_mem_reeFixedTorus hK hh)
    · exact mul_mem (mul_mem (mul_mem (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hu)
        (mem_smallReeInvCentralizer_of_mem_reeFixedTorus hK hh))
        (canonicalRep_mem_smallReeInvCentralizer hw₀))
        (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hv)

end Main
end CFSG.Walter.Ree.Model
end
