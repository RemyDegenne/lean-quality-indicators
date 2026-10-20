public section

namespace CoxeterSystem

variable {B W G : Type*} {M : CoxeterMatrix B} [Group W] [Monoid G]

namespace BraidEquivalent

theorem append_right {word word' : List B} (h : BraidEquivalent M word word')
    (suf : List B) : BraidEquivalent M (word ++ suf) (word' ++ suf) := by
  induction h with
  | rel word word' h => exact of_isBraidMove (h.append_right suf)
  | refl word => exact .refl _
  | symm word word' _ ih => exact ih.symm
  | trans word word' word'' _ _ ih ih' => exact ih.trans ih'

end BraidEquivalent
end CoxeterSystem
end
