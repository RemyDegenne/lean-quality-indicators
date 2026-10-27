public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- **Composition of ambient isotopies**: follow `Φ_t` then `Ψ_t` at each time `t`. -/
def trans (Ψ : AmbientIsotopy Y) : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => Ψ.toContinuousMap (p.1, Φ.toContinuousMap p), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, Ψ.toContinuousMap (p.1, Φ.toContinuousMap p)))
        = ⇑Ψ.totalMap ∘ ⇑Φ.totalMap := by
      funext p
      simp [Function.comp, totalMap_apply]
    rw [heq]
    exact Ψ.isHomeomorph_total.comp Φ.isHomeomorph_total
  map_zero_left' y := by
    -- the composite's `toFun` at time `0` is `Ψ (0, Φ (0, y))`, which both factors fix.
    simp

end AmbientIsotopy
end TauCeti
end
