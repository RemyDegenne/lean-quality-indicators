public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.LocalAnalysis.GLTheoremA.S10

open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem std_single (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {D₀ K : Subgroup G} (hstd : GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K) {y : G} (hy : y ∈ D₀)
    (hya : y ∉ Subgroup.zpowers a) :
    GLAPComponent 3 (cx y) (closureIn K (GLAPLayer 3 (cx y))) ∧
      B ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) ∧
      GLAPComponent 3 (closureIn K (GLAPLayer 3 (cx y)) ⊓ cx a) K := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD₀B, hD₀el, hD₀c, haD₀, hKdef, hKcomp, hDeq⟩ := hstd.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hBel : IsElemAbelian 3 B := B_el h
  have hy1 : y ≠ 1 := fun h1 => hya (h1 ▸ Subgroup.one_mem _)
  have hyB : y ∈ B := hD₀B hy
  have hay3 : a ^ 3 = 1 := hD₀el.2 a haD₀
  have hyy3 : y ^ 3 = 1 := hD₀el.2 y hy
  have hBC : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hay' : a ∉ Subgroup.zpowers y := fun hm => by
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers y := Subgroup.zpowers_le.2 hm
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hyy3 hy1, orderOf_eq_prime hay3 ha1]
    exact hya (Subgroup.eq_of_le_of_card_ge hle hcard ▸ Subgroup.mem_zpowers y)
  have hcsD : cs D₀ = cx a ⊓ cx y := by
    obtain ⟨hDle, -, hDcard⟩ := card_Dgrp hD₀el hp haD₀ hy hy1 hay'
    have hDeq' : Dgrp a y = D₀ := Subgroup.eq_of_le_of_card_ge hDle (by rw [hD₀c, hDcard])
    rw [← hDeq', dgrp_eq_sup, gamma_cs_zpowers_sup]
  have hcsA : cx a ⊓ cs D₀ = cx a ⊓ cx y := by
    rw [hcsD, ← inf_assoc, inf_idem]
  have hJsub : IsSubnormal (Jpart 3 (Ipart 3 L b) a) (cx a) := Jpart_subnormal hc hin.l105 h ha ha1
  have hKa0 : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G)) K :=
    glaPComponent_of_quasisimple hp hKcomp.2.1 hKq (casegamma_three_dvd_quot hin.stdf hKq (hclaim D₀ K hstd))
  have hKa : GLAPComponent 3 (cx y ⊓ cx a) K := by
    have h1 := glaPComponent_of_isSubnormal' hp (isSubnormal_inf hJsub (cs D₀)) hKa0
    rw [hcsA] at h1
    rw [inf_comm]
    exact h1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    intro β hβ
    have hβH : ∀ γ ∈ B, γ ∈ Subgroup.normalizer
        ((Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) :=
      fun γ hγ => casegamma_yS_normalizer_inf ((B_le_N_J hc h ha).2 hγ)
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.2 fun d hd =>
          isElemAbelian_commute hBel (hD₀B hd) hγ))
    have h1 := casegamma_layer_gLBConj_le (hβH β hβ)
    have h2 := casegamma_layer_gLBConj_le (hβH β⁻¹ (B.inv_mem hβ))
    rw [mem_normalizer_iff_gLBConj_eq, hKdef]
    apply le_antisymm h1
    calc GLALayer (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G))
        = GLBConj β (GLBConj β⁻¹ (GLALayer (Jpart 3 (Ipart 3 L b) a ⊓
            Subgroup.centralizer (D₀ : Set G)))) := (gLBConj_gLBConj_inv β _).symm
      _ ≤ GLBConj β (GLALayer (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G))) :=
        CFSG.LocalAnalysis.GLTheoremA.gLBConj_mono (g := β) h2
  have hX : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right (by norm_num) (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y))
  obtain ⟨eK⟩ := S9.nonempty_pSimple_equiv hp hKa hKq
  have hcat : catalogIs (PSimple 3 K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) :=
    (catalogIs_congr eK).2 (hclaim D₀ K hstd)
  obtain ⟨K', hK'c, hKK', hBK'⟩ := hin.single_std (cx y) a B K hX
    (hD₀B haD₀) hBC hBel hrank
    (by rw [S3.centralizer_zpowers a]; exact hKa) hBN hcat
  have hKeq : closureIn K (GLAPLayer 3 (cx y)) = K' := closureIn_layer_eq_of_component hp hK'c hKa hKK'
  have hKa_le : K ≤ cx a := (hKcomp.1.trans inf_le_left).trans (Jpart_le_cx h ha)
  rw [hKeq]
  refine ⟨hK'c, hBK', ?_⟩
  exact glaPComponent_of_le hp hKa (le_inf hKK' hKa_le) (inf_le_inf_right _ hK'c.1)

end S10
end CFSG.LocalAnalysis.GLTheoremA
end
