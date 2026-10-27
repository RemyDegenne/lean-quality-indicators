@[expose] public section

namespace V7.Stage3BelowTwoS3F

/-- The literal below-two primal trajectory starting at the zero normalized state. -/
noncomputable def primalState (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    ℕ → PrimalState d
  | 0 => ⟨0, 0, 0⟩
  | k + 1 =>
      let old := primalState p n oracle k
      let sNext := old.s - increment n k • oracle.gradient old.x
      let vNext := belowMirrorMap p sNext
      let xNext :=
        (weight n k / weight n (k + 1)) • old.x +
        (increment n (k + 1) / weight n (k + 1)) • vNext +
        (increment n k / weight n (k + 1)) • (vNext - old.v)
      ⟨sNext, vNext, xNext⟩

end V7.Stage3BelowTwoS3F
end
