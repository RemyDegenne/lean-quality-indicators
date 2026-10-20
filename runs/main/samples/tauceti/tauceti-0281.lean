public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace TauCeti.MeasureTheory

open scoped ENNReal NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

theorem exists_holderOnWith_preciseRepresentative_of_isCompact [Nonempty ι] :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      IsCompact K → K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, hα, hα1, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_isCompact_drift (mu := mu) (lam := lam)
      (Lam := Lam)
  exact ⟨α, hα, hα1, fun h ha hu hK hKΩ =>
    hhol (beta := 0) h ha aestronglyMeasurable_const (fun _ _ => by simp) hu hK hKΩ⟩

end PDE
end TauCeti
end
end
