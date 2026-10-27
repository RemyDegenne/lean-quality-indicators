@[expose] public section

namespace Connes

namespace BinaryPontryaginDual

noncomputable section

local instance instPointwiseDualTopology {M : Type*} [AddCommGroup M] [Module F M] :
    TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M

/-- The additive binary character underlying a Pontryagin character. Paper: §3.
-/
def characterAdd {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) : M →+ F :=
  { toFun x := Multiplicative.toAdd
      (binaryRootsEquiv.symm
        (characterIntoRoots χ (Multiplicative.ofAdd x)))
    map_zero' := by
      change Multiplicative.toAdd
        (binaryRootsEquiv.symm (characterIntoRoots χ 1)) = 0
      rw [map_one, map_one]
      rfl
    map_add' x y := by
      change Multiplicative.toAdd
          (binaryRootsEquiv.symm
            (characterIntoRoots χ
              (Multiplicative.ofAdd x * Multiplicative.ofAdd y))) = _
      rw [map_mul, map_mul]
      rfl }

end
end BinaryPontryaginDual
end Connes
end
