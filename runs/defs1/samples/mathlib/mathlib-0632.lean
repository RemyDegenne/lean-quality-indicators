@[expose] public section

universe u

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

open Function

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≼i " => InitialSeg

notation3:25 α:24 " ≤i " β:25 => @InitialSeg α β (· < ·) (· < ·)

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≺i " => PrincipalSeg

notation3:25 α:24 " <i " β:25 => @PrincipalSeg α β (· < ·) (· < ·)

open scoped InitialSeg

/-- Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That is, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been used yet.

This construction is guaranteed to work as long as there exists some relation embedding `r ↪r s`. -/
@[no_expose]
noncomputable def RelEmbedding.collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h ↦ by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h ↦ ?_) lt).elim
      by_contra hn
      exact hm' _ hn h
    · rfl
    · exact (hm gt).elim⟩

end
