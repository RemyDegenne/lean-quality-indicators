open MulAction Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

variable {p n : ℕ} {P : Type*} [Group P] {X : Subgroup P}

theorem lt_normalizer_of_natCard_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ n) (hX : X < ⊤) :
    X < normalizer (X : Set P) := by
  refine Subgroup.le_normalizer.lt_of_not_ge fun hle => ?_
  have h1 : X.relIndex (normalizer (X : Set P)) = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h2 := le_relIndex_normalizer hp hP hX
  have := hp.two_le
  omega

end
end CFSG.FeitThompson
