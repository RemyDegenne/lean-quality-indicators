public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits QuadraticMap

open CFSG.ClassicalInvolution.ModelFacts (spinCtx_pOmegaPlus exists_spin_conj
  finrank_perp_add_four map_longSL2_range map_conj_map La_range_eq_map_conj longestFundamental
  fundamentalSubgroups_subset_longest)

open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (longSL2_range_mem_fund)

open CFSG.ClassicalInvolution.Models.OrthogonalPairs (IsFundamental)

open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

open CFSG.ClassicalInvolution.Asc77.Hub (hubFrame hub_unitaryPair hub_ne_std)

open CFSG.LieType.CurtisTits (rankOne)

open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem exists_hub (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) :
    ∃ H : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
      H ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) ∧
      ∀ {i j : Fin 4} (hij : i ≠ j) (s t : Bool),
        H ≠ ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 hij s t).range ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H
          ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 hij s t).range := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have S := spinCtx_pOmegaPlus (p := p) (n := 4) (e := f) le_rfl hp2 hq
  have hodd : Odd (Nat.card (GaloisField p f)) := S.odd_card
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hcard : Nat.card (GaloisField p f) = p ^ f := S.card_eq
  have hneg : ¬ IsSquare (-1 : GaloisField p f) := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq (GaloisField p f) p (-1)
  have hab : (a₀ : GaloisField p f) * a₀ + (b₀ : GaloisField p f) * b₀ = -1 := by
    have := hab₀
    push_cast at this
    linear_combination this
  have h4 : (4 : GaloisField p f) ≠ 0 := by
    have : (4 : GaloisField p f) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hw : 4 * (4 : GaloisField p f)⁻¹ = 1 := mul_inv_cancel₀ h4
  set a : GaloisField p f := (a₀ : GaloisField p f) with ha
  set b : GaloisField p f := (b₀ : GaloisField p f) with hb
  set w : GaloisField p f := 4⁻¹ with hwdef
  have hij₀ : (0 : Fin 4) ≠ 1 := by decide
  set fr₀ := (plusFrame 4 (GaloisField p f) hn3).toFrame hij₀ true false with hfr₀
  have hperp : 2 ≤ Module.finrank (GaloisField p f) fr₀.perp := by
    have := finrank_perp_add_four fr₀
    have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
      simp
    omega
  obtain ⟨x, hx⟩ := exists_spin_conj hodd (nondegenerate_polarBilin_quadPlus 4 (GaloisField p f))
    fr₀ (hubFrame a b w hab hw) hperp
  set R₀ := ((plusFrame 4 (GaloisField p f) hn3).longSL2 hij₀ true false).range with hR₀
  have hR₀fund : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3) := longSL2_range_mem_fund hp2 hq hij₀ true false
  have hHfund : conjSub x R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3) :=
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR₀fund x
  have hHmap : (conjSub x R₀).map (spinAction (quadPlus 4 (GaloisField p f))) =
      (hubFrame a b w hab hw).La.range := by
    unfold conjSub
    rw [map_conj_map, hR₀, map_longSL2_range]
    exact (La_range_eq_map_conj hx).symm
  refine ⟨conjSub x R₀, hHfund, ?_⟩
  intro i j hij s t
  have hRmap := map_longSL2_range (plusFrame 4 (GaloisField p f) hn3) hij s t
  have hRfund : ((plusFrame 4 (GaloisField p f) hn3).longSL2 hij s t).range ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) :=
    longSL2_range_mem_fund hp2 hq hij s t
  have hHlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hHfund
  have hRlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hRfund
  have hpair := hub_unitaryPair (K' := GaloisField p (2 * f)) hcard S.card_eq' hodd hneg hn3 a b w
    hab hw hij s t
  have hpair' : UnitaryBlockStandardPair (GaloisField p (2 * f)) p f
      ((hubFrame a b w hab hw).La.range ⊔
        ((plusFrame 4 (GaloisField p f) hn3).toFrame hij s t).La.range)
      ((conjSub x R₀).map (spinAction (quadPlus 4 (GaloisField p f))))
      (((plusFrame 4 (GaloisField p f) hn3).longSL2 hij s t).range.map
        (spinAction (quadPlus 4 (GaloisField p f)))) := by
    rw [hHmap, hRmap]
    exact hpair
  refine ⟨?_, S.unitary_of_map hHlong hRlong ⟨_, hpair'⟩⟩
  intro hHR
  refine hub_ne_std hn3 a b w hab hw hij s t
    (IsFundamental.involution_unique hodd (L := (hubFrame a b w hab hw).La.range)
      ⟨_, rfl, rfl⟩ ?_)
  rw [← hHmap, hHR, hRmap]
  exact ⟨_, rfl, rfl⟩

end CFSG.ClassicalInvolution.Asc77
end
