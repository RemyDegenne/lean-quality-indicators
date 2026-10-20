@[expose] public section

open Function Polynomial

section PerfectRing

section CommSemiring

variable (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]

variable [PerfectRing R p]

section commute

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)
    [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p]

theorem MonoidHom.map_iterate_frobeniusEquiv_symm (f : R →* S) (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x) := by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    rw [← Function.comp_apply (f := (⇑(frobenius R p))^[n]),
        ← Function.comp_apply (f := (⇑(frobenius S p))^[n]),
        ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate]
    · simp
    all_goals rw [← coe_frobeniusEquiv]; simp [Function.Commute, Function.Semiconj]
  apply Function.Injective.iterate
  simp

end commute
end CommSemiring
end PerfectRing
end
