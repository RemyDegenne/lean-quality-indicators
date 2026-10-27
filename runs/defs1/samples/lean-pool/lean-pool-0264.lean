@[expose] public section

namespace PDL

open Lean4GlCoalgebras

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

/-- Pick a `PreState` for a given `Match`, using `Match.existsPreState` and `List.find?`.
Noncomputable because `Finset.toList` is. -/
noncomputable def Match.toPreState {X} {bt : BuildTree [] X} (m : Match bt) : PreState bt :=
  ⟨(bt.collect.toList.find? m.fitsPreState).get m.findOpt_fitsPreState_isSome,
    Finset.mem_toList.mp (List.mem_of_find?_eq_some (Option.some_get _).symm)⟩

end PDL
end
