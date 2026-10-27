@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]

variable {𝒰} (d : RelativeGluingData 𝒰)

namespace RelativeGluingData

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/--
The glued scheme of a relative gluing datum is the colimit over the `Xᵢ`. For the
structure map, see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase` and the isomorphisms
with the preimages `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase`.
-/
@[stacks 01LH]
noncomputable abbrev glued : Scheme.{u} :=
  colimit d.functor

end RelativeGluingData
end Scheme.Cover
end AlgebraicGeometry
end
