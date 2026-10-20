public section

open Function OrderDual Set

variable {α β : Type*} {ι : Sort*}

open OrderDual

namespace ULift

universe v

@[to_dual]
theorem down_iSup [SupSet α] (f : ι → ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i).down :=
  congr_arg sSup <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm

end ULift
end
