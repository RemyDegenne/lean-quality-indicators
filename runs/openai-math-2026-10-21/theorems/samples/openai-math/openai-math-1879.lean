namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set

open scoped BigOperators

theorem integrable_rawRealIntegrand (N : ℕ) :
    Integrable (fun p => rawRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n N))
    (fun _ => realPlaceMeasure) (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
  apply (hmap.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (n N))).measurableEmbedding).mp
  apply (integrable_pairedDeterminant N).congr
  filter_upwards with z
  exact pairedDeterminant_factor N z

end InternalCatalan
end
end OAI
