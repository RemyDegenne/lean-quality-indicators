@[expose] public section

open scoped unitInterval Topology Topology.Homotopy

namespace Cube

scoped[Topology.Homotopy] notation "∂I^" n => Cube.boundary (Fin n)

scoped[Topology.Homotopy] notation "⊔I^" n => Cube.boundaryJar n

/-- The inclusion from the n-dimensional cube to the top face of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, 1).
(Although `1` appears first in this definition, it is actually the last coordinate
in `(I^ Fin (n + 1))`, due to `Cube.insertAt`). -/
def inclToTop {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := splitAtLast.symm ⟨1, y⟩
  continuous_toFun := splitAtLast.symm.continuous.comp <|
    Continuous.prodMk continuous_const continuous_id

end Cube
end
