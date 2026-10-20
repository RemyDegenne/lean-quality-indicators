public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {T Y : Scheme.{u}} {s : T ⟶ Y}

namespace RigidifiedLineBundleClass

open RigidifiedLineBundle

variable {T' Y' : Scheme.{u}} {s' : T' ⟶ Y'} {h : Y' ⟶ Y} {g : T' ⟶ T}

@[simp]
lemma pullback_inv (w : s' ≫ h = g ≫ s) (a : RigidifiedLineBundleClass s) :
    pullback w a⁻¹ = (pullback w a)⁻¹ := by
  simpa only [pullbackHom_apply] using map_inv (pullbackHom w) a

end RigidifiedLineBundleClass
end
end AlgebraicGeometry
end TauCeti
end
