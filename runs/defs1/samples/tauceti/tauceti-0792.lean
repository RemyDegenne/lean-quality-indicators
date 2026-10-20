public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u v

noncomputable section

variable {T Y : Scheme.{u}}

/-- A line bundle on `Y` rigidified along a morphism `s : T ⟶ Y`: a line bundle `L` on `Y`
together with a trivialization `s^* L ≅ 𝒪_T` of its pullback along `s`. -/
structure RigidifiedLineBundle (s : T ⟶ Y) where
  /-- The underlying line bundle on `Y`. -/
  lineBundle : InvertibleSheaf Y
  /-- The trivialization of the pullback of the line bundle along `s`. -/
  rigidification : (Scheme.Modules.pullback s).obj lineBundle.obj ≅ 𝟙_ T.Modules

end
end AlgebraicGeometry
end TauCeti
end
