@[expose] public section

noncomputable section

namespace SphereOddDegree

open CategoryTheory unitInterval

/-- The monodromy of a homotopy class of paths from `x` to `y`, packaged as a
bundled equivalence between the two fibres of the double cover. This refines
`projMonodromy_bijective`; on loops it specialises to `projMonodromyPerm`. -/
def projMonodromyEquiv (n : ℕ) {x y : RP n} (γ : Path.Homotopic.Quotient x y) :
    (proj n ⁻¹' {x}) ≃ (proj n ⁻¹' {y}) :=
  Equiv.ofBijective _ (projMonodromy_bijective n γ)

end SphereOddDegree
end
end
