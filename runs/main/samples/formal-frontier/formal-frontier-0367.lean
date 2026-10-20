public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

@[simp]
lemma Scheme.mem_connectedComponentOpen (X : Scheme.{u}) [LocallyConnectedSpace X]
    (c : ConnectedComponents X) (x : X) :
    x ∈ X.connectedComponentOpen c ↔ ConnectedComponents.mk x = c := by
  rfl

end AlgebraicGeometry
end
end
