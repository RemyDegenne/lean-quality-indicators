namespace OAI

namespace FiberFunctorProof

open CategoryTheory Representation

universe u

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]

lemma free_relativeTrace (I : Type u) :
    relativeTrace (Representation.free k G I) (Representation.free k G I)
      (freeNormRepresentative I) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro i
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [relativeTrace_apply, Finsupp.finsetSum_apply,
    free_action_apply, freeNormRepresentative_apply]
  simp [Representation.coeff_ofMulAction]

end FiberFunctorProof
end OAI
