@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

local instance intervalRatZero : Zero IntervalRat := ⟨IntervalRat.singleton 0⟩

local instance intervalRatAdd : Add IntervalRat := ⟨IntervalRat.add⟩

local instance : SMul Nat IntervalRat where
  smul n a :=
    { lo := (n : ℚ) * a.lo
      hi := (n : ℚ) * a.hi
      le := mul_le_mul_of_nonneg_left a.le (by positivity) }

local instance : AddCommMonoid IntervalRat :=
  Function.Injective.addCommMonoid
    (fun I : IntervalRat => (I.lo, I.hi))
    (by intro a b h; exact intervalRat_ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Interpret a real matrix as a continuous linear map on finite coordinate vectors. -/
noncomputable def matrixCLM {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

end LeanCert.Engine
end
end
end
end
