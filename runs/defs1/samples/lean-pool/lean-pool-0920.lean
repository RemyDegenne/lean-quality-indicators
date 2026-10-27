@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits ZeroObject

open scoped MonObj

universe v u w

section Biprod

variable {D : Type u}

/-- **The bicone of the module biproduct is a bilimit.** -/
noncomputable def modBinaryBiconeIsBilimit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    (modBinaryBicone A M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (modBinaryBicone_total A M N)

end Biprod
end RS
end
