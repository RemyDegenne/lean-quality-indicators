@[expose] public section

open MeasureTheory InnerProductSpace

open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

namespace FullEllipticOp

variable {d : ℕ} (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The Riesz operator of the `λ`-shifted weak problem: `⟪opAlam u, v⟫ = B[u,v] - λ⟨u₀,v₀⟩`. -/
def opAlam (lam : ℝ) : H01 Ω →L[ℝ] H01 Ω :=
  (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - (Op.gardingγ + lam) • opT Ω

end FullEllipticOp
end EllipticPdes.Sobolev
end
end
