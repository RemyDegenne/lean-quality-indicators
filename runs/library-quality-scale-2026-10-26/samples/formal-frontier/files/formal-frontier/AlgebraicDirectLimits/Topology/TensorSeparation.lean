/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorHom
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff preservation statements for one-sided tensors

The statements concern the existing `TopModuleCat.tensorLeftObj`: its left
factor is algebraic and only its right factor carries a topology. One statement
takes an arbitrary supplied basis; the other takes a projective coefficient
module, without exposing a basis or a splitting to the caller. The scalar ring
is any commutative ring with a supplied topology; joint scalar continuity is
part of the right-factor bundle. All carrier and index universes are independent.

The product-coordinate map in `Topology.TensorHom` has an arbitrary index;
the coordinate equivalences and their finite-sum inverses in
`Topology.TensorProduct` remain finite-only.

## Limitations

These are forward preservation statements, not Hausdorffness reflection.
Empty bases and trivial scalar rings are allowed.
No compactness result, completed tensor product, coefficient topology or global
Hausdorffness instance is introduced.

## References

The finite-coordinate construction is the existing one in
`AlgebraicDirectLimits.Topology.TensorProduct`, by Formal Frontier Agents,
following the earlier coinduced-module and Continuous Group Cohomology
one-sided topology development, including Beacon's original development.
Mathlib's tensor-basis API is due to Jakob von Raumer, and its finite-free
chosen-basis API to Riccardo Brasca. The Hausdorff and product separation APIs
are due to Johannes Hölzl and Mario Carneiro. The continuous-linear-equivalence
API is due to Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov,
Frédéric Dupuis and Heather Macbeth; the homeomorphism API is due to Johannes
Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou and Reid Barton.
The arbitrary-basis and split-cover route follows Lantern's mathematics.
Mathlib's projective-module definition and split-summand API are due to Kevin
Buzzard and Antoine Labelle; the Finsupp basis and coefficient APIs are due to
Johannes Hölzl, Kim Morrison, Mario Carneiro and Alexander Bentkamp.
The original topological-module development is due to Richard Hill and Andrew Yang.
-/

@[expose] public section

universe uR uC uM uι

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

/-- A supplied coefficient basis, with arbitrary index, preserves Hausdorffness
of the right factor in the one-sided tensor product. -/
theorem t2Space_tensorLeftObj_of_basis {ι : Type uι}
    (b : Module.Basis ι R C) [T2Space M] : T2Space (tensorLeftObj R C M) := by
  exact T2Space.of_injective_continuous
    (tensorCoordinatesCLM_injective R C M b)
    (tensorCoordinatesCLM R C M b).continuous

/-- Tensoring a Hausdorff topological module on the left with an algebraic
projective coefficient module preserves Hausdorffness. -/
theorem t2Space_tensorLeftObj [Module.Projective R C] [T2Space M] :
    T2Space (tensorLeftObj R C M) := by
  let F : ModuleCat.{max uR uC} R := ModuleCat.of R (C →₀ R)
  let π : F →ₗ[R] C := Finsupp.linearCombination R (id : C → C)
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := R) (P := C)).mp
    (inferInstance : Module.Projective R C)
  let i : tensorLeftObj R C M →L[R] tensorLeftObj R F M :=
    tensorMapCLM R (C := C) (D := F) (M := M) (N := M) s
      (ContinuousLinearMap.id R M)
  let p : tensorLeftObj R F M →L[R] tensorLeftObj R C M :=
    tensorMapCLM R (C := F) (D := C) (M := M) (N := M) π
      (ContinuousLinearMap.id R M)
  let : T2Space (tensorLeftObj R F M) :=
    t2Space_tensorLeftObj_of_basis R F M
      (Finsupp.basisSingleOne : Module.Basis C R F)
  have hπs : π.comp (show C →ₗ[R] F from s) = (LinearMap.id : C →ₗ[R] C) := hs
  have hsplit : p.comp i = ContinuousLinearMap.id R (tensorLeftObj R C M) :=
    tensorMapCLM_comp_eq_id R (C := C) (D := F) (M := M) (N := M) s π
      (ContinuousLinearMap.id R M) (ContinuousLinearMap.id R M) hπs
      (ContinuousLinearMap.id_comp (ContinuousLinearMap.id R M))
  have hleft : Function.LeftInverse p i :=
    ContinuousLinearMap.leftInverse_of_comp hsplit
  exact T2Space.of_injective_continuous hleft.injective i.continuous

end TopModuleCat
