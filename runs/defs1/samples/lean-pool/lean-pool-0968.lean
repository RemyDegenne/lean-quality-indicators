@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

namespace KnownTerm

/-- Mean raw, with branches according to `k.zeroMean`. -/
def meanRaw (k : KnownTerm) (O : Operators) (p : ℕ) (a : ℕ → Profile) (i j : ℕ) : VectorField :=
  if k.zeroMean then 0 else angleMean O.period (k.raw O p a i j)

end KnownTerm
end EulerPacketCylinderField
end
end
