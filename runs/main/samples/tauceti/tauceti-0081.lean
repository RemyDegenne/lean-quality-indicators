public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

section ArrowHom

variable (k : Type u) {Q : Type v} [Field k] [Quiver.{w} Q]

theorem indecProjRepBasis_repr_indecProjRepArrowHom_app {i j b : Q} (e : i ⟶ j)
    (x : (indecProjRep k Q j).obj ((Paths.of Q).obj b)) :
    (indecProjRepBasis k i b).repr ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b) x)
      = Finsupp.mapDomain (fun q : Quiver.Path j b ↦ e.toPath.comp q)
          ((indecProjRepBasis k j b).repr x) := by
  have key : (indecProjRepBasis k i b).repr.toLinearMap ∘ₗ
        ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b)).hom
      = Finsupp.lmapDomain k k (fun q : Quiver.Path j b ↦ e.toPath.comp q) ∘ₗ
          (indecProjRepBasis k j b).repr.toLinearMap :=
    (indecProjRepBasis k j b).ext fun q ↦ by
      refine (congrArg (indecProjRepBasis k i b).repr (indecProjRepArrowHom_app_basis k e q)).trans
        ?_
      simp [Finsupp.mapDomain_single]
  exact LinearMap.congr_fun key x

end ArrowHom
end TauCeti
end
