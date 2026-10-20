namespace MisereGames

open Form

open Form.Misere.Outcome

open GameForm

open OutcomeStable

universe u

public section

variable {A : GameForm → Prop}

namespace IntegerInvertible

theorem misereOutcome_add_neg_NTippingPoint_N_of_misereOutcome_R {g : GameForm}
    [PFree A]
    (hA : A g) (hsg : IsShort g) (hR : MisereOutcome g = .R) :
    MisereOutcome (g + (-(NTippingPoint hsg : GameForm))) = .N := by
  have := NTippingPoint_spec hsg
  contrapose! this
  constructor
  · intro h
    have := PFree.misereOutcome_add_natCast_R_of_misereOutcome_R (NTippingPoint hsg) hA hR
    simp_all +decide
  · exact this

end IntegerInvertible
end
end MisereGames
