namespace OAI

noncomputable section

open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.MetricBlock

open scoped Classical

variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

theorem adj_symm {x y : X} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨G.reverse e, G.move_reverse x e⟩

end DiscreteFree.MetricBlock
end
end
end OAI
