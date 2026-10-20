@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Extend a map to a sober space by sending each irreducible closed subset to the
generic point of the closure of its image. This realizes the extension in
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Proposition 2.1.3,
via the open-intersection characterization, not the proof cited there. -/
noncomputable def extend [QuasiSober Y] [T0Space Y] (f : C(X, Y)) :
    C(IrreducibleCloseds X, Y) :=
  ⟨fun F => (map f f.continuous F).isIrreducible.genericPoint, by
    rw [continuous_def]
    intro S hS
    let V : Opens Y := ⟨S, hS⟩
    convert (openSet ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage f.continuous⟩).isOpen using 1
    ext F
    exact (((map f f.continuous F).isIrreducible.isGenericPoint_genericPoint
      (map f f.continuous F).isClosed).mem_open_set_iff V.isOpen).trans
        (map_mem_openSet_iff f F V)⟩

end TopologicalSpace.IrreducibleCloseds
end
