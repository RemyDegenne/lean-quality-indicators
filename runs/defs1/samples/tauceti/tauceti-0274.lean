public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits MulOpposite

universe u

namespace FGModuleCat

variable {A : Type u} [Ring A]

variable [IsNoetherianRing Aᵐᵒᵖ]

section TruncatedPolynomial

open Polynomial

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n i : ℕ}

/-- Over `R[X]/(X ^ n)`, with `x` the class of `X` and `M_i = A ⧸ (x ^ i)`, the module `M_i` is
periodic of period at most two in the stable module category: `Ω² M_i ≅ M_i` for `i ≤ n`. -/
noncomputable def stableModuleLoopLoopCyclicModuleRootPowIso (hi : i ≤ n) :
    (stableModuleLoop (AdjoinRoot (X ^ n : R[X]))).obj ((stableModuleLoop _).obj
        ((stableModuleFunctor _).obj (cyclicModule (AdjoinRoot.root (X ^ n : R[X]) ^ i)))) ≅
      (stableModuleFunctor _).obj (cyclicModule (AdjoinRoot.root (X ^ n : R[X]) ^ i)) :=
  stableModuleLoopLoopCyclicModuleIso (AdjoinRoot.root_X_pow_pow_mul_eq_zero_iff hi)
    (AdjoinRoot.root_X_pow_sub_pow_mul_eq_zero_iff hi)

end TruncatedPolynomial
end FGModuleCat
end TauCeti
end
