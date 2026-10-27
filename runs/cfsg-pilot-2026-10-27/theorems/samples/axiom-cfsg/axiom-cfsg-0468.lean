public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section PhaseB

variable {X B K : Subgroup G} {y : G}

theorem exists_k0Data {x : G} (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 81)
    (hSC : IsSCp 3 ⊤ B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R)
    (hiso : Nonempty (↥(GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
        GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) ≃*
        (↥(barX 3 (Subgroup.centralizer ({x} : Set G)) K) ⧸
          Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) K))))
    (hcomp0 : GLAPComponent 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))
      (GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)))) :
    K0Data B K x y (GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hB
  set X := Subgroup.centralizer ({x} : Set G) with hX
  set K₀ := GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)) with hK₀
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hB ha hb
  have hBX : B ≤ X := fun b hb => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact hcomm b hb x hxB
  have hle : K₀ ≤ bClosure B K ⊓ Subgroup.centralizer ({y} : Set G) :=
    sSup_le fun L hL => hL.1
  have hK₀B : B ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro b hb
    rw [mem_normalizer_iff_gLBConj_eq, hK₀, ← layer_gLBConj, gLBConj_inf, bClosure_conj_eq hb,
      gLBConj_centralizer_of_comm (hcomm b hb y hy)]
  obtain ⟨S₀, hS₀K, hS₀p, hS₀c, hS₀B⟩ := exists_invariant_sylow (p := 3) hBp hK₀B
  obtain ⟨φ⟩ := hiso
  obtain ⟨hS9, hSel⟩ := k0_sylow_facts hK hR.heis inf_le_right hR.c1 hR.hc1 φ hS₀K hS₀p hS₀c
  obtain ⟨hcard, hne, hinf⟩ := card_centralizerQuot_le hB hBc hSC hK₀B hS₀B hS₀K hSel hS₀c
    (by rw [hS9]; norm_num) (fun g hg hc => k0_centreless hK φ hg hc)
  have hKX := bClosure_le_of_comp hB hBX hK hy hyN h3
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_centralizer hK.1
  have hxy : x * y = y * x := hcomm x hxB y hy
  have hx3 := hB.2 x hxB
  have hy3 := hB.2 y hy
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ Subgroup.one_mem _)
  have hne' : Subgroup.zpowers x ≠ Subgroup.zpowers y := by
    intro h
    apply hyN
    have : y ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.2 hxN) this
  have h9 := card_zpowers_sup hxy hx3 hy3 hx1 hy1 hne'
  have hmemcq : ∀ g ∈ B, (∀ k ∈ K₀, k * g * k⁻¹ * g⁻¹ = 1) →
      g ∈ B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) := fun g hg hcg =>
    ⟨hg, hK₀B hg, normalizer_core 3 (hK₀B hg), fun k hk => by
      rw [hcg k hk]; exact Subgroup.one_mem _⟩
  have hxcq := hmemcq x hxB (fun k hk => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hKX (hle hk).1)
    calc k * x * k⁻¹ * x⁻¹ = x * k * k⁻¹ * x⁻¹ := by rw [h]
      _ = 1 := by group)
  have hycq := hmemcq y hy (fun k hk => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hle hk).2
    calc k * y * k⁻¹ * y⁻¹ = y * k * k⁻¹ * y⁻¹ := by rw [h]
      _ = 1 := by group)
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) :=
    sup_le (Subgroup.zpowers_le.2 hxcq) (Subgroup.zpowers_le.2 hycq)
  have hcqeq : B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) =
      Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    (Subgroup.eq_of_le_of_card_ge hsup (by rw [h9]; exact hcard)).symm
  refine ⟨hcomp0, hle, hK₀B, ⟨S₀, hS₀K, hSel, hS9⟩, hcqeq, hne, ?_⟩
  rw [hcqeq] at hinf
  exact hinf

end PhaseB
end CFSG.HardMathSupport.Solomon.UniquenessMaximal
end
