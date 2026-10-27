@[expose] public section

universe u

open CategoryTheory

attribute [instance] Preord.str

namespace Preord

/-- The type of morphisms in `Preord R`. -/
@[ext]
structure Hom (X Y : Preord.{u}) where
  _mkInternal ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

end Preord
end
