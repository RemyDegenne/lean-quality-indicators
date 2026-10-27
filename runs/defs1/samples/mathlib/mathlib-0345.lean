@[expose] public section

universe u

open CategoryTheory

attribute [instance] UniformSpaceCat.str

attribute [instance] isUniformSpace isCompleteSpace isT0

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

/-- The inclusion of a uniform space into its completion. -/
noncomputable def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  hom'.val := ((↑) : X → Completion X)
  hom'.property := Completion.uniformContinuous_coe X

end UniformSpaceCat
end
