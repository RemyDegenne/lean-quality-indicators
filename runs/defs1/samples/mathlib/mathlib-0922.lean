@[expose] public section

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

variable {P : TopCat.{u} → Prop}

namespace LightCondMod.LocallyConstant

open LightCondensed

variable (R : Type u) [Ring R]

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteAux₁ (M : ModuleCat.{u} R) :
    M ≅ ↧(LocallyConstant (LightProfinite.of PUnit.{u + 1}) M) where
  hom := ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

end LightCondMod.LocallyConstant
end
