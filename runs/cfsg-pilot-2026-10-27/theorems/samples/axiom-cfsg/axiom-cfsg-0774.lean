public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem FusedPGL.inv {X : Type} [Group X] {z : X} {E : Subgroup X} {n : X} {q : ℕ}
    (h : FusedPGL z E n q) : FusedPGL z E n⁻¹ q := by
  rw [FusedPGL, Subgroup.zpowers_inv]
  obtain ⟨Z, hZC, hZB, hzZ, hsq, hn⟩ := h
  refine ⟨Z, hZC, hZB, hzZ, ?_, hn⟩
  rw [← mul_inv_rev]
  exact (E ⊔ Z).inv_mem hsq

end CFSG.GH74.GLS.Stage1.Main
end
