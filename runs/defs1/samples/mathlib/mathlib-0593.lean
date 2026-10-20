@[expose] public section

variable {α β γ : Type*}

namespace Function

variable (f : α → β)

section LT

variable [LT β] [WellFoundedLT β]

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α` is finite. -/
@[to_dual
/-- Given a function `f : α → β` where `β` carries a well-founded `>`, this is an element of `α`
whose image under `f` is maximal in the sense of `Function.not_argmax_lt`.

See also `Set.Finite.exists_maximalFor` and related lemmas for the case when `α` is finite. -/]
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

end LT
end Function
end
