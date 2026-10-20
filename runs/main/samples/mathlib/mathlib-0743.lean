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

namespace FiniteDimensional

variable [Unique ι] (h : Module.finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1)

theorem range_orthonormalBasisSingleton :
    Set.range (orthonormalBasisSingleton ι 𝕜 h v hv) = {v} := by
  simp

end FiniteDimensional
end
end
