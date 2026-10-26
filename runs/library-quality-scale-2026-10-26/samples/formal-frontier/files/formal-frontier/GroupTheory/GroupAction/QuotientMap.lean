/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant maps between nested coset spaces

For subgroups `H ≤ K` of a group `G`, `MulActionHom.quotientMapOfLE` bundles the
canonical map `G ⧸ H → G ⧸ K` as an equivariant map for left multiplication.
Neither subgroup is required to be normal, and neither coset space is required
to be finite.

The map sends the class of each `g : G` to its class modulo `K`. It is surjective,
preserves identities and composition, and commutes with `MulActionHom.toQuotient`.
When both coset spaces are finite, its underlying function agrees with
`Action.FintypeCat.quotientToQuotientOfLE`.

## References

The construction uses Mathlib's `Subgroup.quotientMapOfLE`, the quotient actions
from `Mathlib.GroupTheory.GroupAction.Quotient`, and the equivariant-map API of
`MulActionHom`. It generalizes the finite-coset construction
`Action.FintypeCat.quotientToQuotientOfLE` from
`Mathlib.CategoryTheory.Action.Concrete`.
-/

@[expose] public section

universe u

namespace MulActionHom

variable {G : Type u} [Group G] {H K L : Subgroup G}

/-- The equivariant map from left cosets of `H` to left cosets of `K` induced
by an inclusion `H ≤ K`. Its underlying function is `Subgroup.quotientMapOfLE`. -/
def quotientMapOfLE (h : H ≤ K) : (G ⧸ H) →[G] G ⧸ K where
  toFun := Subgroup.quotientMapOfLE h
  map_smul' g q := by
    refine Quotient.inductionOn' q ?_
    intro a
    simp only [MulAction.Quotient.smul_mk, Subgroup.quotientMapOfLE_apply_mk, id_eq]

/-- Forgetting equivariance gives the canonical map between coset spaces. -/
@[simp] theorem coe_quotientMapOfLE (h : H ≤ K) :
    ⇑(quotientMapOfLE h) = Subgroup.quotientMapOfLE h :=
  rfl

/-- Every representative maps to its class modulo the larger subgroup. -/
@[simp] theorem quotientMapOfLE_apply_mk (h : H ≤ K) (g : G) :
    quotientMapOfLE h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  Subgroup.quotientMapOfLE_apply_mk h g

/-- The map associated to the identity inclusion is the identity equivariant map. -/
@[simp] theorem quotientMapOfLE_refl (H : Subgroup G) :
    quotientMapOfLE (le_refl H) = MulActionHom.id G := by
  apply MulActionHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  simp only [quotientMapOfLE_apply_mk, MulActionHom.id_apply]

/-- Maps between coset spaces compose according to subgroup inclusion. -/
@[simp] theorem quotientMapOfLE_comp (h : H ≤ K) (k : K ≤ L) :
    (quotientMapOfLE k).comp (quotientMapOfLE h) = quotientMapOfLE (h.trans k) := by
  apply MulActionHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  simp only [MulActionHom.comp_apply, quotientMapOfLE_apply_mk]

/-- The equivariant map induced by a subgroup inclusion is surjective. -/
theorem quotientMapOfLE_surjective (h : H ≤ K) :
    Function.Surjective (quotientMapOfLE h) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk g, quotientMapOfLE_apply_mk h g⟩

/-- Projection to `G ⧸ H` followed by the map to `G ⧸ K` is projection to `G ⧸ K`. -/
@[simp] theorem quotientMapOfLE_comp_toQuotient (h : H ≤ K) :
    (quotientMapOfLE h).comp (toQuotient H) = toQuotient K := by
  apply MulActionHom.ext
  intro g
  simp only [MulActionHom.comp_apply, toQuotient_apply, quotientMapOfLE_apply_mk]

/-- On finite coset spaces, the underlying function agrees with Mathlib's
morphism of finite `G`-sets. Only the two coset spaces need to be finite. -/
theorem quotientMapOfLE_eq_quotientToQuotientOfLE
    [Fintype (G ⧸ H)] [Fintype (G ⧸ K)] (h : H ≤ K) :
    (quotientMapOfLE h : G ⧸ H → G ⧸ K) =
      fun q => (Action.FintypeCat.quotientToQuotientOfLE K H h).hom q := by
  funext q
  refine Quotient.inductionOn' q ?_
  intro g
  exact (quotientMapOfLE_apply_mk h g).trans
    (Action.FintypeCat.quotientToQuotientOfLE_hom_mk K H h g).symm

end MulActionHom
