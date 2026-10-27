@[expose] public section

section SourceScanMax

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {A : Type*} [Fintype A] [DecidableEq A]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

variable [LinearOrder A]

/-- The maximum scan of the input itself: the value map is the identity. -/
noncomputable def maxScan (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι A A (WithBot A) :=
  maxScanMap id rk hrk

end QuantumQueryComplexity
end SourceScanMax
end
