@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits.Types

variable (C : Type u) [Category.{v} C]

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (constPUnitFunctor.{w} C) ≅ PUnit.{w + 1} :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

end Limits.Types
end CategoryTheory
end
