@[expose] public section

universe uR uS uM uN

open CategoryTheory

open scoped TensorProduct

namespace ModuleCat.RightExtension

section RingTarget

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S]

variable (φ : R →+* S)

theorem tensorFunctor_map_apply {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N)
    (x : (tensorFunctor φ).obj M) :
    (tensorFunctor φ).map g x =
      @TensorProduct.map R R _ _ (RingHom.id R)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _ _ _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
        (@LinearMap.id R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule) x := by
  change ((tensorFunctor φ).map g).hom x = _
  rw [tensorFunctor_map_hom]
  exact tensorProductMap_apply φ g x

end RingTarget
end ModuleCat.RightExtension
end
