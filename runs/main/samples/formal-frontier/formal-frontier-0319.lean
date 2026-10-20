@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

@[simp]
theorem HomColimit.continuousHomEquiv_apply
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (x : HomColimit G F) :
    HomColimit.continuousHomEquiv G F x =
      HomColimit.toContinuousHom G F x :=
  rfl

end ProfiniteGrp.FiniteQuotientHom
end
