@[expose] public section

open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp

noncomputable section

variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

syntax (name := PiLp.vecNotation) "!" noWs subscriptTerm noWs "[" term,* "]" : term

macro_rules | `(!$p:subscript[$e:term,*]) => do
  -- override the `Fin n.succ` to a literal
  let n := e.getElems.size
  `(WithLp.toLp $p (V := ∀ _ : Fin $(quote n), _) ![$e,*])

variable (ι 𝕜)

variable {ι 𝕜}

variable (ι 𝕜 E)

variable [Fintype ι]

variable {ι 𝕜 E}

open Module

section FiniteDimensional

variable {v : Set E}

variable {A : ι → Submodule 𝕜 E}

variable [FiniteDimensional 𝕜 E]

variable (𝕜 E)

/-- A finite-dimensional `InnerProductSpace` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)

end FiniteDimensional
end
end
