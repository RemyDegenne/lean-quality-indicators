namespace OAI

section

section

namespace ElementaryPositivity.QuantumTorus

open PowerSeries ElementaryPositivity.PowerSeriesSplit

noncomputable section

variable {R M I A : Type*} [CommRing R] [AddCommGroup M] [Fintype I]

variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (h : M →+ ℝ)

local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

lemma chartZero_leading_difference (f g : CompletedPositive v Ω C) (n : ℕ)
    (hlow : ∀k≤n,coeff k f.val=coeff k g.val) :
    coeff (n+1) (chartZero v Ω C h f).val-
      coeff (n+1) (chartZero v Ω C h g).val=
      zeroProject v Ω h (coeff (n+1) f.val-coeff (n+1) g.val) :=
  zero_leading_difference (positiveProject v Ω h) (zeroProject v Ω h)
    (zero_positive_project v Ω h) f.val g.val n hlow

end
end ElementaryPositivity.QuantumTorus
end
end
end OAI
