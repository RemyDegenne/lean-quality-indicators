public section

namespace TauCeti.DenseGraphLimits

variable {k : ℕ}

namespace LabeledGraph

@[simp]
theorem forgetLabels_fullyLabeled {n : ℕ} (G : SimpleGraph (Fin n)) :
    (fullyLabeled G).forgetLabels = ⟨n, G⟩ := (rfl)

end LabeledGraph
end TauCeti.DenseGraphLimits
end
