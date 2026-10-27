public section

noncomputable section

namespace TauCeti

namespace DenseGraphLimits

open MeasureTheory

/-- The edge coordinates of a graph on `Fin n`, with its labels read in `ℕ`. -/
def windowCoord {n : ℕ} (H : SimpleGraph (Fin n)) : EdgeIndex → Bool :=
  graphCoordEquiv (H.map Fin.valEmbedding)

end DenseGraphLimits
end TauCeti
end
end
