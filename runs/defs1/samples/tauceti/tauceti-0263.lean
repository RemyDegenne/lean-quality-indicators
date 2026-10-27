public section

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace NormalizedCubicalChain

open SingularCube

/-- The homomorphism from the normalized integral cubical `(n + 2)`-chains of `X` to
`π_{n+2}(X, x)` that sends the class of an `(n + 2)`-based cube, a generalized loop, to its
homotopy class (`TauCeti.SingularCube.basedClass`), and the class of every other cube to zero. It
is well defined on normalized chains because a degenerate based cube is constant. -/
def basedClassHom (x : X) (n : ℕ) :
    NormalizedCubicalChain X ℤ (n + 2) →ₗ[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x) :=
  (CubicalChain.degenerate X ℤ (n + 2)).liftQ
    (Finsupp.linearCombination ℤ fun c ↦ Additive.ofMul (basedClass x c)) <| by
      rw [CubicalChain.degenerate_def, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      simp [basedClass_of_isDegenerate hc]

end NormalizedCubicalChain
end TauCeti
end
end
