public noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u

namespace TopPair

variable (k : Type u) [Ring k]

/-- On relative cubical chains, the comparison maps compose to the identity up to the
homotopy induced by the natural acyclic-models homotopy on absolute cubical chains. -/
def cubicalToSingularRelCompHomotopy (P : TopPair.{u}) :
    _root_.Homotopy (cubicalToSingularRel k P ≫ singularToCubicalRel k P) (𝟙 _) :=
  _root_.Homotopy.descCokernel (cubicalToSingularCompHomotopy k P.fst)
    ((normalizedCubicalChainComplex k).map P.map)
    (cokernel.π _) (cokernel.π _)
    (fun n ↦ by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
        congrArg (fun (φ : _ ⟶ P.cubicalChainComplex k) ↦ φ.f n) (cokernel.condition _))
    (fun n ↦ isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.down ℕ) n) _)
    (fun i j ↦ by
      rw [← Category.assoc, cubicalToSingularCompHomotopy_hom_naturality, Category.assoc,
        ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero])
    (by
      rw [π_cubicalToSingularRel_assoc, Category.assoc, singularRelπ_singularToCubicalRel])
    (by simp)

end TopPair
end
