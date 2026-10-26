/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import SmoothRegularity.SmoothAt

/-!
# Regular local stalks on the smooth locus

This file transports the affine smooth-at-prime regularity criterion to schemes
locally of finite type over a field.
-/

public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A point in the smooth locus of a scheme locally of finite type over a field
has a regular local stalk. -/
theorem Scheme.Hom.isRegularLocalRing_of_mem_smoothLocus
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X}
    (hx : x ∈ f.smoothLocus) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let _ := ((Scheme.ΓSpecIso ↧K).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have : (f.appLE ⊤ U (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  let q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hq : Algebra.IsSmoothAt Γ(Spec (.of K), ⊤) q :=
    (formallySmooth_stalkMap_iff (⊤ : (Spec (.of K)).Opens)
      (isAffineOpen_top _) U hU (by simp) hxU).mp
      (Scheme.Hom.mem_smoothLocus.mp hx)
  have hreg : IsRegularLocalRing (Localization.AtPrime q) :=
    Algebra.IsSmoothAt.isRegularLocalRing q hq
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let e := IsLocalization.algEquiv q.primeCompl
    (X.presheaf.stalk x) (Localization.AtPrime q)
  exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

end AlgebraicGeometry
