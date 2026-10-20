public section

open scoped Topology

universe u

variable {G α X : Type*} [TopologicalSpace X]

export ContinuousInv (continuous_inv)

export ContinuousNeg (continuous_neg)

export ContinuousSub (continuous_sub)

export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

variable {f g : X → G} {s : Set X} {x : X}

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
nonrec theorem ContinuousAt.div' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f / g) x :=
  hf.div' hg

end ContinuousDiv
end
