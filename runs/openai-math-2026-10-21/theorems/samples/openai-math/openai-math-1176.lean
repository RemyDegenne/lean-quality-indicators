namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

open scoped Classical

variable {I ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem realSymbolFactorization_freeze
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℝ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : I => 1)).Group)
    (E P R : F.RealPolynomialSymbolGroup (fun _ : I => 1))
    (hfactor : E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ : I => 1) g)
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : I => 1) U))
    (T : I → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hE : F.SymbolSlowBound b ω hF (fun _ : I => 1) T M E)
    (q : ℕ) (hR : F.SymbolRationalGrid b ω hF (fun _ : I => 1) q R) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fun _ : I => 1)
      (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep)
    pull E * pull P * pull R = F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep fixed) (frozenCoordinate_support keep fixed) g) ∧
    (pull P).coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) U) ∧
    F.SymbolSlowBound b ω hF (fun _ : {i // keep i} => 1) (fun i => T i.val) M (pull E) ∧
    F.SymbolRationalGrid b ω hF (fun _ : {i // keep i} => 1) q (pull R) := by
  intro pull
  have hsymbolZero := F.realPolynomialSymbolHom_homogeneousChart b ω hF
    (fun _ : I => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
    (frozenCoordinate_zero_homogeneous keep) g
    (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
      (frozenCoordinate keep 0) (frozenCoordinate_support keep 0) g)
    (F.weightedAdaptedRealChartHom_coord _ _ _ _ g)
  have hfiber : F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep 0) (frozenCoordinate_support keep 0) g) =
      F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep fixed) (frozenCoordinate_support keep fixed) g) := by
    simpa only [freezePolynomial, aeval_X] using
      F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : I => 1)
        (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : I => 1) i)
        keep 0 fixed g
  refine ⟨?_, F.realSymbolHomogeneousPullback_mem_pointwise b ω hF _ _ _ _ U P hP,
    F.symbolSlowBound_freeze_zero b ω hF keep T hT hM E hE, ?_⟩
  · calc
      _ = pull (E * P * R) := by rw [map_mul, map_mul]
      _ = pull (F.realPolynomialSymbolHom b ω hF (fun _ : I => 1) g) := congrArg pull hfactor
      _ = _ := hsymbolZero.symm.trans hfiber
  · apply F.symbolRationalGrid_homogeneousPullback_integral b ω hF
      (fun _ : I => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep) ?_ q R hR
    intro i
    have hcast : MvPolynomial.map (Int.castRingHom ℝ)
        (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i) =
        frozenCoordinate keep (0 : {i // ¬keep i} → ℝ) i := by
      by_cases hi : keep i <;> simp [frozenCoordinate, hi]
    exact hcast ▸ realPolynomialCoefficientGrid_intCast
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i)

end Erdos3.NilpotentLieFiltration
end
end OAI
