public section

noncomputable section

open MeasureTheory

open scoped ENNReal unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Constant

open Classical in
@[simp]
theorem sampleMass_const (p : I) (G : SimpleGraph (Fin n)) :
    sampleMass (Graphon.const μ p) G =
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
  have hfactor (x : Fin n → Ω) (e : Sym2 (Fin n)) :
      edgeFactor (Graphon.const μ p) x e = (p : ℝ) := by
    induction e using Sym2.ind with
    | _ a b => simp
  have hcard : ((⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset).card =
      n.choose 2 - G.edgeFinset.card := by
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr (SimpleGraph.edgeFinset_mono le_top)]
    congr 1
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  rw [sampleMass_def]
  have hintegrand : sampleIntegrand (Graphon.const μ p) G = fun _ =>
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
    funext x
    rw [sampleIntegrand]
    simp_rw [hfactor x]
    rw [Finset.prod_const, Finset.prod_const, hcard]
  rw [hintegrand]
  simp

end Constant
end DenseGraphLimits
end TauCeti
end
end
