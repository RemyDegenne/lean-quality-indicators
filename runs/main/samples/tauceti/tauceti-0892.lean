public section

namespace TauCeti.Sporadic.Lyons

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

theorem map_length_relators_presentation :
    presentation.relators.map List.length =
      [8, 5, 8, 6, 12,
        5, 40, 18, 22, 22, 22, 24, 24, 20, 12, 20, 7, 15, 19, 26, 18, 16, 18,
        18, 2, 9, 16, 13, 18, 22, 13, 22, 22, 28, 6, 4, 6, 45, 29,
        13, 13, 12, 12, 21, 6, 10, 14, 4, 20, 50, 46, 83, 43] := by
  simp only [GroupPresentation.relators_def, presentation_transcribed, Relator.commInvInv,
    Relator.conj, Relator.div, List.map_cons, List.map_nil, Relator.toWord_gen, Relator.toWord_inv,
    Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_comm]
  decide

end TauCeti.Sporadic.Lyons
end
