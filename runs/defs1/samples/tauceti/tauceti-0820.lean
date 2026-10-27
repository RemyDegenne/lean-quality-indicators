public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

variable (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]

variable (hL : L.IsEven) (hM : M.IsEven)

variable (e : FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
  (M.discriminantQuadraticModule hM).neg)

/-- The second lattice's integral inclusion into the graph-glued overlattice. -/
noncomputable def glueRight : M →ₗ[ℤ] L.glueAlongDiscriminant M hL hM e :=
  ((LinearMap.inr ℤ V W).comp M.carrier.subtype).codRestrict _
    (fun y ↦ (L.mem_glueAlongDiscriminant_right_iff M hL hM e y).mpr y.2)

end TauCeti.IntegralLattice
end
