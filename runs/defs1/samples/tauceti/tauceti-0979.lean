public section

namespace TauCeti.Toric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ τ : PointedCone ℝ V}

namespace ToricRay

/-- The rays of a cone `σ` contained in a finitely generated face `τ`, as a finite set: the image of
the rays of `τ` under `faceEmbedding`. -/
noncomputable def faceFinset (hτ : τ.IsFaceOf σ) (hfg : τ.FG) : Finset (ToricRay σ) :=
  have := finite_of_fg hfg
  (Set.finite_range (faceEmbedding hτ)).toFinset

end ToricRay
end TauCeti.Toric
end
