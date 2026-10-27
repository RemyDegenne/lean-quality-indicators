public section

universe u v w x y

namespace Module.Free

noncomputable section

variable (R : Type u) [Ring R]

/-- Removing a finite-coordinate free summand from a module equivalent to the
countable free module does not change the module's isomorphism type. -/
def natFinsuppEquivOfProdFinFinsuppEquiv
    {P : Type v} [AddCommGroup P] [Module R P]
    (m : ℕ) (h : (P × FiniteFree R m) ≃ₗ[R] CountableFree R) :
    P ≃ₗ[R] CountableFree R := by
  let j : FiniteFree R m →ₗ[R] CountableFree R :=
    h.toLinearMap.comp (LinearMap.inr R P (FiniteFree R m))
  let s : Finset ℕ := finiteImageSupport R m j
  let e : (P × FiniteFree R m) ≃ₗ[R]
      ((s : Set ℕ) →₀ R) × (((s : Set ℕ)ᶜ : Set ℕ) →₀ R) :=
    h.trans (coordinateSplit R (s : Set ℕ))
  have hQ :
      (LinearMap.snd R ((s : Set ℕ) →₀ R)
          (((s : Set ℕ)ᶜ : Set ℕ) →₀ R)).comp
        (e.toLinearMap.comp (LinearMap.inr R P (FiniteFree R m))) = 0 := by
    apply LinearMap.ext
    intro q
    change (coordinateSplit R (s : Set ℕ) (h (0, q))).2 = 0
    apply coordinateSplit_snd_eq_zero_of_support_subset
    simpa [j, s] using support_image_subset_finiteImageSupport R m j q
  exact
    (blockSwindle R e hQ (finiteComplAbsorbFinite R s m)).trans
      (coordinateSplit R (s : Set ℕ)).symm

end
end Module.Free
end
