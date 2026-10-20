set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

lemma boundaryToOneKer_comm [TopRep.JointlyContinuous X] :
    boundaryToOneKer X ≫ (oneKerCrossedIso X).hom =
      (cochainsZeroIso X).hom ≫
        TopModuleCat.ofHom (principalToCrossedL X) := by
  ext σ g
  change σ.1 g - σ.1 1 = X.ρ g (σ.1 1) - σ.1 1
  have hinv := congrArg (fun f : C(G, X) => f g) (σ.2 g)
  simp only [ContRepresentation.coind₁_apply_apply] at hinv
  rw [← hinv]
  simp

end ContinuousCohomology
end
