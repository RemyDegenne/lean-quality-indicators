public section

namespace TauCeti.Hodge

open scoped DirectSum

universe u

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

variable {ω : Conjugation W} {n : ℤ}

theorem piece_le_conjF_of_lt (hs : HodgeStructureOn W ω n) {p q : ℤ} (hqp : q < p) :
    hs.piece q ≤ hs.conjF (n + 1 - p) :=
  (hs.piece_le_conjF q).trans (hs.conjF_antitone (by omega))

end HodgeStructureOn
end TauCeti.Hodge
end
