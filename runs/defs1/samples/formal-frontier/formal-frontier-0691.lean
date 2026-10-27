@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

section CoefficientChange

variable {S : Type w} [CommRing S] (f : R →+* S)

/-- The trace-zero subalgebra's underlying additive groups under coefficient change. -/
def slMap : LieAlgebra.SpecialLinear.sl n R →+
    LieAlgebra.SpecialLinear.sl n S where
  toFun X := ⟨(X.1 : Matrix n n R).map f, by
    change ((X.1 : Matrix n n R).map f).trace = 0
    rw [← AddMonoidHom.map_trace f X.1]
    have hx : (X.1 : Matrix n n R).trace = 0 := X.property
    rw [hx, map_zero]⟩
  map_zero' := by apply Subtype.ext; ext i j; simp
  map_add' X Y := by apply Subtype.ext; ext i j; simp

end CoefficientChange
end Matrix.DualNumberKernels
end
