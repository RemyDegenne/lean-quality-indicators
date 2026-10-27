public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem exists_line_of_uniqueW_gen (h : EndHyp Ω) (h9 : Perp9 Ω) {a : G} (ha : a ≠ 1)
    {R R' : Subgroup G} {r : G} (s : TwinSit Ω R R' r) (hR : R ∈ centMembers Ω a)
    (hR' : R' ∈ centMembers Ω a) (hne : centMembers Ω a ≠ {R, R'})
    (hW : ∃ W₀ : Subgroup G, WIn (centMembers Ω a) (pSpan (centMembers Ω a)) = {W₀}) :
    ∃ b : G, (∃ T ∈ centMembers Ω a, IsUniqueInvolution T b) ∧ b ≠ r ∧
      b ∈ Subgroup.normalizer (R : Set G) ∧
      {x | ∃ L ∈ centMembers Ω a, IsUniqueInvolution L x} = {r, b, r * b} := by
  have hΩ := h.thmD.hyp
  obtain ⟨hcard, hstar⟩ := h.section_six_of_uniqueW h9 ha s hR hR' hne hW
  have hinv : ∀ L ∈ centMembers Ω a, ∀ x ∈ pSpan (centMembers Ω a),
      conjSub x L ∈ centMembers Ω a := fun L hL x hx =>
    h.toStarHyp.conjSub_mem_centMembers hL hx
  obtain ⟨T, hTP, hT⟩ : ∃ T ∈ centMembers Ω a, T ∉ ({R, R'} : Set (Subgroup G)) := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hcon (Set.insert_subset_iff.mpr
      ⟨hR, Set.singleton_subset_iff.mpr hR'⟩))
  have hTR : T ≠ R := fun e => hT (Or.inl e)
  have hstarT : T ∈ omegaStarNbr Ω R := hstar R hR T hTP hTR
  have hnotT : T ∉ omegaNbr Ω R := fun hn => by
    rw [mem_omegaNbr_iff_of_perp9 h h9 hR.1, s.twin] at hn
    exact hT hn.1
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution hΩ hTP.1
  have hbr : b ≠ r := by
    intro e
    have hTt : T ∈ twinSet Ω R := ⟨hTP.1, r, s.isInv, e ▸ hb⟩
    rw [s.twin] at hTt
    exact hT hTt
  obtain ⟨-, -, -, hV4, -, -⟩ := pair_structure h hR.1 hstarT hnotT
  have hbN : b ∈ Subgroup.normalizer (R : Set G) :=
    (hb.mem_of_le (inf_le_left : T ⊓ Subgroup.normalizer (R : Set G) ≤ T)
      ((h.thmD.two T hTP.1).to_le inf_le_left) (by omega)).2
  obtain ⟨τ, hτT, hτN⟩ : ∃ τ ∈ T, τ ∉ Subgroup.normalizer (R : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnotT ⟨hTP.1, hTR, T, TC.mem_RSet_of_isPGroup hTP.1 (h.thmD.two T hTP.1), le_rfl,
      hcon⟩
  have hτ := conj_involution_eq_mul h hR.1 hstarT hnotT s.isInv hb hτT hτN
  have hτP : conjSub τ R ∈ centMembers Ω a := hinv R hR τ (le_pSpan hTP hτT)
  have hRτ : IsUniqueInvolution (conjSub τ R) (r * b) := by
    have := s.isInv.conj τ
    rwa [hτ] at this
  have hcls : ∀ M ∈ centMembers Ω a,
      twinSet Ω M ⊆ centMembers Ω a ∧ (twinSet Ω M).ncard = 2 := by
    intro M hM
    refine ⟨h.twinSet_subset_centMembers h9 ha s hR hR' hne M hM, ?_⟩
    obtain ⟨M', hMM', hM'⟩ := h.twinSet_pair s hM.1
    rw [hM', Set.ncard_pair hMM'.symm]
  have hdisj : ∀ {M N : Subgroup G} {x y : G}, IsUniqueInvolution M x →
      IsUniqueInvolution N y → x ≠ y → Disjoint (twinSet Ω M) (twinSet Ω N) := by
    intro M N x y hx hy hxy
    refine Set.disjoint_left.mpr fun J hJM hJN => ?_
    obtain ⟨-, z₁, hz₁M, hz₁J⟩ := hJM
    obtain ⟨-, z₂, hz₂N, hz₂J⟩ := hJN
    exact hxy ((hx.eq hz₁M).trans ((hz₁J.eq hz₂J).trans (hz₂N.eq hy)))
  have hrb : r ≠ r * b := fun e =>
    hb.ne_one (mul_left_cancel (a := r) (by rw [mul_one]; exact e.symm))
  have hbrb : b ≠ r * b := fun e =>
    s.isInv.ne_one (mul_right_cancel (a := r) (b := b) (c := 1) (by rw [one_mul]; exact e.symm))
  refine ⟨b, ⟨T, hTP, hb⟩, hbr, hbN, ?_⟩
  ext x
  constructor
  · rintro ⟨L, hLP, hLx⟩
    by_contra hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    obtain ⟨hxr, hxb, hxrb⟩ := hx
    obtain ⟨h1sub, h1c⟩ := hcls R hR
    obtain ⟨h2sub, h2c⟩ := hcls T hTP
    obtain ⟨h3sub, h3c⟩ := hcls _ hτP
    obtain ⟨h4sub, h4c⟩ := hcls L hLP
    have hd12 := hdisj s.isInv hb (Ne.symm hbr)
    have hd13 := hdisj s.isInv hRτ hrb
    have hd14 := hdisj s.isInv hLx (Ne.symm hxr)
    have hd23 := hdisj hb hRτ hbrb
    have hd24 := hdisj hb hLx (Ne.symm hxb)
    have hd34 := hdisj hRτ hLx (Ne.symm hxrb)
    have hsub : twinSet Ω R ∪ twinSet Ω T ∪ twinSet Ω (conjSub τ R) ∪ twinSet Ω L ⊆
        centMembers Ω a :=
      Set.union_subset (Set.union_subset (Set.union_subset h1sub h2sub) h3sub) h4sub
    have hc : (twinSet Ω R ∪ twinSet Ω T ∪ twinSet Ω (conjSub τ R) ∪ twinSet Ω L).ncard = 8 := by
      rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
          ⟨Set.disjoint_union_left.mpr ⟨hd14, hd24⟩, hd34⟩),
        Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Set.ncard_union_eq hd12, h1c, h2c, h3c, h4c]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨R, hR, hx ▸ s.isInv⟩
    · exact ⟨T, hTP, hx ▸ hb⟩
    · exact ⟨conjSub τ R, hτP, hx ▸ hRτ⟩

end EndHyp
end CFSG.ClassicalInvolution.Q3.Sec13
end
