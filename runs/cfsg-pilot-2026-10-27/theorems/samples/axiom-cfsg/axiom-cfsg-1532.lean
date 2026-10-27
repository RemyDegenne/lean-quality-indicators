public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (hσ : ∀ c, σ (σ c) = c)

section QV

variable {sg h : ℤ} {e : Fin (n / 2) → ℤ}

theorem QV.mul (hsg : sg ≠ 0) (hh : 0 < h) (he : e ≠ 0)
    (hlev1 : ∀ a b : Fin n, weight n a - weight n b = e → lvl sg b - lvl sg a = h)
    (hlev2 : ∀ a b : Fin n, weight n a - weight n b = 2 • e → lvl sg b - lvl sg a = 2 * h)
    {M N : Matrix (Fin n) (Fin n) F} (hM : QV sg h e M) (hN : QV sg h e N) : QV sg h e (M * N) :=
  ⟨idBelow_mul _ hh hM.1 hN.1, fun a b hab => by
    rw [mul_apply_of_qv hsg hh he hlev1 hlev2 hM.1 hN a b hab, hM.2 a b hab]⟩

end QV
end CFSG.LieType.Universal.Unitary.SUExtras
end
