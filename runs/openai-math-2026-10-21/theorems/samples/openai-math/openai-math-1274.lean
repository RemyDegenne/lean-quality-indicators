namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V B J K : Type*} (Q : ReversibleQuiver V B)

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)

namespace StringFunctor

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

local notation "U" => Q.stringQuiver step hstep N hN

local notation "I" => StringIndex (V := V) N

omit [Fintype V] in
lemma arrowImage_eq_zero_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) (h : i.old ≠ (U).source p) :
    arrowImage Q step hstep N hN orient μ A p i j = 0 := by
  exact ite_eq_right (fun h' => h h'.1)

end StringFunctor
end HarmonicArtin.ReversibleQuiver
end OAI
