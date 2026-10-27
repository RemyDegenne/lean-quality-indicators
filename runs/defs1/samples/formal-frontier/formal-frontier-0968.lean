@[expose] public section

universe u v w z

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

section TrivialMap

variable {G : Type v} [Monoid G]

/-- Every continuous linear coefficient map intertwines trivial group actions. -/
def trivialMap {H : Type z} [Monoid H] {B C : TopRep.{w} k G} (φ : B →L[k] C) :
    TopRep.of (ContRepresentation.trivial k H B) ⟶
      TopRep.of (ContRepresentation.trivial k H C) :=
  ofHom {
    toContinuousLinearMap := φ
    isIntertwining' := by
      intro h
      ext b
      rfl
  }

end TrivialMap
end TopRep
end
