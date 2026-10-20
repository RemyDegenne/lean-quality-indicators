@[expose] public section

noncomputable section

open scoped Nat

open Real Finset

namespace LiouvilleNumber

/-- `LiouvilleNumber.partialSum` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def partialSum (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), 1 / m ^ i !

end LiouvilleNumber
end
end
