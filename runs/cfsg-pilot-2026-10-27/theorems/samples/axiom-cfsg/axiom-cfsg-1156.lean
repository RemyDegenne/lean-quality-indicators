public section

namespace CFSG.EvenSporadicStandard.M22Std

open Equiv CFSG.Blueprint CFSG.EvenSporadicStandard.M22Std.TabCheck

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem length_spanE {G : Type*} [Monoid G] (gs : List G) :
    (spanE gs).length = 2 ^ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [spanE, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    omega

end CFSG.EvenSporadicStandard.M22Std
end
