@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/--
The mass that first hits `A` exactly at step `k`.

For `k = 0` this is the initial mass already inside `A`, and for `k + 1` it is the mass
propagated from the surviving mass at step `k` into `A`.
-/
noncomputable def firstHitMassAtStep {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ENNReal
  | 0 => ∑' n : ℕ, A.indicator (initialMass x Y) n
  | k + 1 =>
      ∑' n : ℕ,
        A.indicator
          (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

end PrimitiveSetsAboveX
end
