public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n

open scoped commutatorElement

variable {G : Type} [Group G]

open Aff

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}

include H

theorem aC_sq_eq_one (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {c : G} (hc : c ∈ H.aC g) :
    c * c = 1 := by
  obtain ⟨n, hn, hnat, hpart, htrans, hKel, hKform, hWA, hA, hcomm, hrel, K₁, hK₁X, hK₁B, hK₁Bg,
    hK₁cyc, hK₁card, hK₁A, hK₁fpf, hK₁pts⟩ := h1
  have hc2B : c * c ∈ B := by
    have := H.sq_mem (H.aC_le_Q hc)
    rwa [pow_two] at this
  have hWK : B ⊔ conjSubgroup g B ≤ kernel48 B T g := by
    show _ ≤ (T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)
    rw [hKform]; exact le_sup_left
  have hAK : T ⊓ conjSubgroup g T ≤ kernel48 B T g := by
    show _ ≤ (T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)
    rw [hKform]; exact le_sup_right
  have hcK : ∀ k ∈ kernel48 B T g, c * k = k * c := by
    intro k hk
    have hk' : k ∈ (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) := by rw [← hKform]; exact hk
    obtain ⟨w, hw, a, ha, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun a ha w hw => comm_of_isElemAbelian hKel (hAK ha) (hWK hw)) hk'
    have hca : c * a = a * c :=
      Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ha.1) c hc.1
    calc c * (w * a) = (c * w) * a := by group
      _ = (w * c) * a := by rw [H.aC_cent_W h48 hcent hc w hw]
      _ = w * (c * a) := by group
      _ = w * (a * c) := by rw [hca]
      _ = (w * a) * c := by group
  have hX : ∀ h ∈ T ⊔ conjSubgroup g T, h * (c * c) * h⁻¹ = c * c := by
    intro h hh
    have hk := H.aC_comm_mem_kernel h48 htrans hcent hc hh
    set k := ⁅h, c⁆ with hkdef
    have hkc : c * k = k * c := hcK k hk
    have hkk : k * k = 1 := IsElemAbelian.mul_self_eq_one hKel hk
    have e1 : h * c * h⁻¹ = k * c := by simp only [hkdef, commutatorElement_def]; group
    calc h * (c * c) * h⁻¹ = (h * c * h⁻¹) * (h * c * h⁻¹) := by group
      _ = (k * c) * (k * c) := by rw [e1]
      _ = k * (c * k) * c := by group
      _ = k * (k * c) * c := by rw [hkc]
      _ = (k * k) * (c * c) := by group
      _ = c * c := by rw [hkk, one_mul]
  have hK₁ne : K₁ ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h, Subgroup.card_bot] at hK₁card
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₁ne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  exact hK₁fpf x hx hx1' (c * c) hc2B (hX x (hK₁X hx))

end Hyp4
end CFSG.RankThree.GF2n.Tim78
end
