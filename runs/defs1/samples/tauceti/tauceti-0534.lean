public section

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The `n`-dimensional cells of `K`: its faces with `n + 1` vertices. -/
abbrev RealizationCell (K : AbstractSimplicialComplex ι) (n : ℕ) :=
  {σ : TauCeti.SetLike.Face K // σ.1.card = n + 1}

end AbstractSimplicialComplex
end
end
