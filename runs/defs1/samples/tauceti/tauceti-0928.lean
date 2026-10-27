public section

namespace TauCeti.Toric

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The canonical fan morphism from any fan to the fan of a point. -/
noncomputable def Fan.toPoint (Φ : Fan i) : FanHom Φ pointFan :=
  FanHom.ofLatticeMap Φ pointFan 0 fun σ hσ ↦ by
    refine ⟨⊥, ?_, ?_⟩
    · exact (mem_pointFan_cones ⊥).2 rfl
    · exact le_of_eq (Subsingleton.elim _ _)

end TauCeti.Toric
end
