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

namespace OrthonormalBasis

section Singleton

variable {ι 𝕜 : Type*} [Unique ι] [RCLike 𝕜]

@[simp]
theorem singleton_apply (i) : OrthonormalBasis.singleton ι 𝕜 i = 1 := Basis.singleton_apply _ _ _

end Singleton
end OrthonormalBasis
end
end
