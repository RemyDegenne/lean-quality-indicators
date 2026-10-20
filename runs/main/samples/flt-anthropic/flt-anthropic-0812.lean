namespace P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical

open IntermediateField AlgebraicCurve ModularCurve Polynomial

namespace W7G2G

section Image

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)

local notation "kk" => IsLocalRing.ResidueField A

local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

set_option maxHeartbeats 6400000 in

theorem resHom_mem_fullC
    (hfin : Module.finrank (IntermediateField.adjoin L {(jF N : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (f : gaussRing A N) : resHom A N f ∈ modularFunctionFieldFullC kk N := by
  set K0 := IntermediateField.adjoin L {(jF N : FF)} with hK0
  set K0' := IntermediateField.adjoin kk {(jbar N kk : Fb)} with hK0'
  set n := Module.finrank K0' Fb with hn
  haveI : Module.Finite K0' Fb := Module.finite_of_finrank_pos hpos
  haveI : Module.Finite K0 FF := Module.finite_of_finrank_pos (by rw [hfin]; exact hpos)
  let bbar := Module.finBasisOfFinrankEq K0' Fb hn.symm
  have hb : ∀ i, ∃ b : gaussRing A N, resHom A N b = ((bbar i : Fb) : LaurentSeries kk) :=
    fun i => exists_resHom_eq A N (bbar i).2
  choose b hb using hb
  let v : Option (Fin n) → FF := fun o => o.elim (f : FF) (fun i => (b i : FF))
  have hdep : ¬ LinearIndependent K0 v := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hfin] at h
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun o => (gaussRing A N).valuation ((g o : K0) : FF)) Finset.univ_nonempty
  have hgi₀ : ((g i₀ : K0) : FF) ≠ 0 := by
    intro h0
    apply hi₁
    have := hi₀ i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ZeroMemClass.coe_eq_zero.mp this
  have hvpos : 0 < (gaussRing A N).valuation ((g i₀ : K0) : FF) := (Valuation.pos_iff _).mpr hgi₀

  let c : Option (Fin n) → FF := fun o => ((g o : K0) : FF) / ((g i₀ : K0) : FF)
  have hcK : ∀ o, c o ∈ K0 := fun o => div_mem (g o).2 (g i₀).2
  have hcO : ∀ o, c o ∈ gaussRing A N := fun o => by
    rw [← (gaussRing A N).valuation_le_one_iff]
    show (gaussRing A N).valuation (_ / _) ≤ 1
    rw [map_div₀, div_le_one₀ hvpos]
    exact hi₀ o (Finset.mem_univ o)
  have hci₀ : c i₀ = 1 := div_self hgi₀
  have hrel : ∑ o, c o * v o = 0 := by
    have h1 : ∑ o, ((g o : K0) : FF) * v o = 0 := by
      simpa only [IntermediateField.smul_def, smul_eq_mul] using hg
    calc ∑ o, c o * v o = ((g i₀ : K0) : FF)⁻¹ * ∑ o, ((g o : K0) : FF) * v o := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun o _ => by simp only [c]; ring
      _ = 0 := by rw [h1, mul_zero]

  have ht : ∀ o, ∃ t : K0', ((t : Fb) : LaurentSeries kk) = resHom A N ⟨c o, hcO o⟩ :=
    fun o => exists_adjoin_coe_eq_resHom A N (hcK o) (hcO o)
  choose t ht using ht
  have hti₀ : t i₀ = 1 := by
    have h1 : (⟨c i₀, hcO i₀⟩ : gaussRing A N) = 1 := Subtype.ext hci₀
    have h2 : ((t i₀ : Fb) : LaurentSeries kk) = (((1 : K0') : Fb) : LaurentSeries kk) := by
      rw [ht i₀, h1, map_one]; simp
    exact Subtype.ext (Subtype.ext h2)

  let w : Option (Fin n) → gaussRing A N := fun o => o.elim f b
  have hvw : ∀ o, v o = (w o : FF) := by rintro (_ | _) <;> rfl
  have hrelO : ∑ o, (⟨c o, hcO o⟩ : gaussRing A N) * w o = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    (first | exact hrel | simpa only [hvw] using hrel | (have h__ := hrel; simp only [hvw] at h__; exact h__))
  have hres : ∑ o, ((t o : Fb) : LaurentSeries kk) * resHom A N (w o) = 0 := by
    have := congrArg (resHom A N) hrelO
    simpa only [map_sum, map_mul, map_zero, ht] using this
  have hwn : resHom A N (w none) = resHom A N f := rfl
  have hws : ∀ i, resHom A N (w (some i)) = ((bbar i : Fb) : LaurentSeries kk) := fun i => hb i
  rw [Fintype.sum_option, hwn] at hres
  simp only [hws] at hres

  by_cases htn : t none = 0
  · exfalso
    have hsum : ∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk) = 0 := by
      simpa only [htn, ZeroMemClass.coe_zero, zero_mul, zero_add] using hres
    have hsum' : (∑ i, t (some i) • bbar i : Fb) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      (first | exact hsum | simpa only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul] using hsum | (have h__ := hsum; simp only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul] at h__; exact h__))
    have hall := Fintype.linearIndependent_iff.mp bbar.linearIndependent (fun i => t (some i)) hsum'
    have : t i₀ = 0 := by
      rcases i₀ with _ | i
      · exact htn
      · exact hall i
    rw [hti₀] at this
    exact one_ne_zero this
  · have htn' : ((t none : Fb) : LaurentSeries kk) ≠ 0 := by
      intro h; apply htn
      exact Subtype.ext (Subtype.ext (by simpa using h))
    have key : resHom A N f =
        -(∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk)) /
          ((t none : Fb) : LaurentSeries kk) := by
      rw [eq_div_iff htn', eq_neg_iff_add_eq_zero, mul_comm]
      exact hres
    rw [key]
    exact div_mem (neg_mem (sum_mem fun i _ => mul_mem (t (some i) : Fb).2 (bbar i).2)) (t none : Fb).2

end Image
end W7G2G
end
end P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
