@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

section Chart

variable (LQ : Type s) [CommRing LQ]
  [Algebra (CoordinateRing A) LQ] [Algebra A LQ]
  [IsScalarTower A (CoordinateRing A) LQ] [IsLocalization.Away (w A) LQ]

/-- The inverse polynomial assignment `W, Y, T ↦ w, y, x / w` in any model of the chart. -/
noncomputable def inversePolynomial : ParameterPolynomial A →ₐ[A] LQ :=
  MvPolynomial.aeval ![algebraMap (CoordinateRing A) LQ (w A),
    algebraMap (CoordinateRing A) LQ (y A),
    algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A)]

end Chart
end SplitQuadric
end
end
