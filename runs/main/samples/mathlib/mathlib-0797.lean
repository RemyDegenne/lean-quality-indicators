@[expose] public section

open Set Filter

open scoped Topology SetRel Uniformity

universe u v ua ub uc ud

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open uniformity

section Constructions

section Prod

open UniformSpace

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

end Prod
end Constructions
end
