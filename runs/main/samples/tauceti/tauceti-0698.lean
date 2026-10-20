public section

namespace TauCeti.Sporadic

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

theorem suzPresentation_relatorsCyclicallyReduced :
    suzPresentation.relatorsCyclicallyReduced := by
  -- Only the relator compiler needs unfolding: once the transcribed expressions are compiled away,
  -- the words are closed data and the kernel decides the predicate.
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    suzPresentation_transcribed, List.map_cons, List.map_nil, Relator.toWord_mul,
    Relator.toWord_pow, Relator.toWord_inv, Relator.toWord_gen, FreeGroup.invRev]
  decide

end TauCeti.Sporadic
end
