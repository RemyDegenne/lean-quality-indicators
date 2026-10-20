@[expose] public section

universe u v w

namespace ProfiniteGrp

theorem isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq
    (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (hH : IsProcyclic H) :
    Nonempty (G ≃ₜ* H) ↔ hG.exponents = hH.exponents := by
  constructor
  · rintro ⟨e⟩
    exact hG.exponents_equiv hH e
  · intro heq
    have eG : G ≃ₜ* Multiplicative
        (primewisePadicQuotientModel.{0} hH.exponents) := by
      exact Eq.mp (congrArg (fun exponents : Nat.Primes → ℕ∞ =>
        G ≃ₜ* Multiplicative (primewisePadicQuotientModel.{0} exponents)) heq)
        hG.continuousMulEquivModel
    exact ⟨eG.trans hH.continuousMulEquivModel.symm⟩

end ProfiniteGrp
end
