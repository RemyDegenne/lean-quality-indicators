@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

@[simp]
theorem HomColimit.continuousHomEquiv_symm_apply
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (q : G →ₜ* F) :
    (HomColimit.continuousHomEquiv G F).symm q =
      HomColimit.ofContinuousHom G F q :=
  rfl

end ProfiniteGrp.FiniteQuotientHom
end
