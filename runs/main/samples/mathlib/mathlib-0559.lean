public section

variable {α β M : Type*}

open Set Filter

@[to_additive]
theorem Monotone.mulIndicator_eventuallyEq_iUnion {ι} [Preorder ι] [One β] (s : ι → Set α)
    (hs : Monotone s) (f : α → β) (a : α) :
    (fun i => mulIndicator (s i) f a) =ᶠ[atTop] fun _ ↦ mulIndicator (⋃ i, s i) f a := by
  classical exact hs.piecewise_eventually_eq_iUnion f 1 a

end
