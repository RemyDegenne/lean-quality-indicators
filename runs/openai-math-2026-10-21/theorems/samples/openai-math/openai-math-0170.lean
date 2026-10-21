namespace OAI

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open scoped BigOperators ComplexConjugate

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory ProbabilityTheory Real Complex

open scoped ENNReal ComplexConjugate

open ProbabilityTheory

namespace HardSphere

open MeasureTheory Set Filter PeriodicCutoff TightCutoff

open scoped ComplexConjugate

open scoped Classical

lemma closeLabels_insert_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} (r : ℝ)
    (w : S → SmoothMultiplier 1 L)
    (hsep : ∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r)
    (v z : S) (X : Configuration (n+1) L) (hx : (w v).orbital (X 0)≠0) :
    (closeLabels r (w z) X).card ≤ (closeLabels r (w z) (Fin.tail X)).card+(if v=z then 1 else 0) := by
  classical
  have he : Fin.cons (X 0) (Fin.tail X)=X := by funext i; cases i using Fin.cases <;> rfl
  rw [←he,closeLabels_cons]
  simp only [Fin.tail_cons]
  by_cases hvz : v=z
  · subst v
    simp only [ite_true]
    split_ifs <;> omega
  · have hzv : z≠v := Ne.symm hvz
    rw [ite_eq_right hvz,ite_eq_right (hsep z v hzv (X 0) hx)]

end HardSphere
end
end OAI
