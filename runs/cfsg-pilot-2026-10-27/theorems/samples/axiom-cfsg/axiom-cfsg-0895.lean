public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement Matrix Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem SectionAct.comm_sup_inf_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (hZV : Z ≤ V) {s t : S} (hs2 : (s : G) * s = 1)
    (ht2 : (t : G) * t = 1)
    (hr : LinearMap.range (act (φ s) - 1).mulVecLin ⊓
      LinearMap.range (act (φ t) - 1).mulVecLin = ⊥) :
    (⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z) ⊓ (⁅V, Subgroup.zpowers (t : G)⁆ ⊔ Z) = Z := by
  obtain ⟨hN, hZn, ψ, hψ⟩ := h
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro g ⟨hgs, hgt⟩
  have hgV := comm_sup_le_of_normalizer hN hZV s.2 hgs
  have h1 := (mem_comm_sup_iff_of_coord hN ψ hψ hZV hs2 hgV).mp hgs
  have h2 := (mem_comm_sup_iff_of_coord hN ψ hψ hZV ht2 hgV).mp hgt
  have h3 : _ ∈ (⊥ : Submodule K (ι → K)) := hr ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩
  rw [Submodule.mem_bot] at h3
  exact (coord_eq_zero_iff ψ ⟨g, hgV⟩).mp h3

end CFSG.RankThree.GF2n.Smith81
end
