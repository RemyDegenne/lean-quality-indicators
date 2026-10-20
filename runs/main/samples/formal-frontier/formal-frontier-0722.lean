@[expose] public section

universe uR uS uT vR vS vT

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

theorem submoduleOrderIsoOfEquivalence_trans
    {T : Type uT} [Ring T]
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S)
    (f : ModuleCat.{vS} S ≌ ModuleCat.{vT} T) (X : ModuleCat.{vR} R) :
    submoduleOrderIsoOfEquivalence (e.trans f) X =
      (submoduleOrderIsoOfEquivalence e X).trans
        (submoduleOrderIsoOfEquivalence f (e.functor.obj X)) := by
  apply OrderIso.ext
  funext N
  change submoduleOrderIsoOfEquivalence (e.trans f) X N =
    submoduleOrderIsoOfEquivalence f (e.functor.obj X)
      (submoduleOrderIsoOfEquivalence e X N)
  rw [submoduleOrderIsoOfEquivalence_apply (e.trans f),
    submoduleOrderIsoOfEquivalence_apply e]
  exact (submoduleOrderIsoOfEquivalence_range f
    (e.functor.map (ofHom N.subtype))).symm

end ModuleCat
end
