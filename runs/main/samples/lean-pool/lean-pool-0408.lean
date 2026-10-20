@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

theorem IsRealStable.isRealStableOrZero
    {σ : Type*} {p : MvPolynomial σ ℝ} (hp : IsRealStable p) :
    IsRealStableOrZero p :=
  Or.inr hp

end BeyondBethe
end
