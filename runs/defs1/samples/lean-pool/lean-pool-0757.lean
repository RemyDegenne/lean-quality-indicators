@[expose] public section

open Filter Set Topology

namespace Wallace

namespace RationalAssembly

noncomputable section

open RationalTriangularPreprocess

open RationalData

open BlockData

open RationalClosure

open RationalFusionRun

open RationalTransfiniteExtension

/-- The block-size schedule used by the assembled rational construction. -/
abbrev N : ℕ → ℕ := RationalFusionRun.blockSize

end
end RationalAssembly
end Wallace
end
