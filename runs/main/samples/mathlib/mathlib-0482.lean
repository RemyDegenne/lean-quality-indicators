@[expose] public section

open Function

variable {T : Type*}

section closure_reversal

namespace ContextFreeGrammar

variable {g : ContextFreeGrammar T} {u v : List (Symbol T g.NT)}

set_option backward.defeqAttrib.useBackward true in
@[simp] lemma language_reverse : g.reverse.language = g.language.reverse := by ext; simp

end ContextFreeGrammar
end closure_reversal
end
