/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Algebra.Group.Submonoid.Saturation

/-!
# Cofinal submonoids and additive group completion

For an arbitrary additive commutative monoid, a submonoid whose saturation is top
is cofinal: every element has an ambient complement whose sum belongs to the
submonoid. The canonical map to the Grothendieck additive group is then a
localization at this submonoid. This gives denominators in the submonoid,
stabilization of equal images there, and injectivity of the group-completion
map induced by its inclusion. No cancellation is required in the monoid.
-/

public section

namespace Algebra.GrothendieckAddGroup

universe u

variable {M : Type u} [AddCommMonoid M] (L : AddSubmonoid M)

/-- If `L` is cofinal, the canonical group-completion map localizes `M` at `L`. -/
theorem isLocalizationMap_of_saturation_eq_top (hL : L.saturation = ⊤) :
    AddSubmonoid.IsLocalizationMap L (of (M := M)) := by
  have cofinal (m : M) : ∃ c : M, m + c ∈ L :=
    AddSubmonoid.mem_saturation_iff.mp (by rw [hL]; trivial)
  refine ⟨fun _ => AddGroup.isAddUnit _, ?_, ?_⟩
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).surj z
    obtain ⟨c, hc⟩ := cofinal (b : M)
    refine ⟨(a + c, ⟨(b : M) + c, hc⟩), ?_⟩
    change z + of ((b : M) + c) = of (a + c)
    change z + of (b : M) = of a at hab
    rw [map_add, map_add, ← add_assoc]
    exact congrArg (fun w => w + of c) hab
  · intro x y hxy
    obtain ⟨t, ht⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).exists_of_eq hxy
    obtain ⟨c, hc⟩ := cofinal (t : M)
    refine ⟨⟨(t : M) + c, hc⟩, ?_⟩
    change ((t : M) + c) + x = ((t : M) + c) + y
    simpa only [add_assoc, add_left_comm, add_comm] using congrArg (fun w => w + c) ht

private def completionLocalizationMap (hL : L.saturation = ⊤) :
    L.LocalizationMap (GrothendieckAddGroup M) where
  toAddHom := (of (M := M)).toAddHom
  isLocalizationMap := isLocalizationMap_of_saturation_eq_top L hL

/-- Every element of the group completion has a numerator in `M` and a denominator in `L`. -/
theorem exists_cofinal_denominator (hL : L.saturation = ⊤) (z : GrothendieckAddGroup M) :
    ∃ m : M, ∃ l : L, z = of m - of (l : M) := by
  obtain ⟨⟨m, l⟩, h⟩ := (completionLocalizationMap L hL).surj z
  exact ⟨m, l, eq_sub_iff_add_eq.mpr h⟩

/-- Two canonical images agree exactly when their representatives stabilize by an element
of the cofinal submonoid. -/
theorem of_eq_iff_exists_cofinal_stabilizer (hL : L.saturation = ⊤) (m n : M) :
    of m = of n ↔ ∃ l : L, m + (l : M) = n + (l : M) := by
  have h := (completionLocalizationMap L hL).eq_iff_exists (x := m) (y := n)
  change of m = of n ↔ ∃ l : L, (l : M) + m = (l : M) + n at h
  simpa only [add_comm] using h

/-- The map on group completions induced by the actual inclusion `L ↪ M` is injective. -/
theorem lift_subtype_injective (hL : L.saturation = ⊤) :
    Function.Injective (lift ((of (M := M)).comp L.subtype)) := by
  have himage : (⊤ : AddSubmonoid L).map L.subtype = L := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  let f := AddLocalization.addMonoidOf (⊤ : AddSubmonoid L)
  let k : ((⊤ : AddSubmonoid L).map L.subtype).LocalizationMap (GrothendieckAddGroup M) :=
    { toAddHom := (of (M := M)).toAddHom
      isLocalizationMap := by
        rw [himage]
        exact isLocalizationMap_of_saturation_eq_top L hL }
  let hy : ∀ y : (⊤ : AddSubmonoid L), L.subtype y ∈ (⊤ : AddSubmonoid L).map L.subtype :=
    fun y => ⟨y, y.property, rfl⟩
  have heq : f.map hy k = lift ((of (M := M)).comp L.subtype) := by
    apply (lift (M := L) (G := GrothendieckAddGroup M)).symm.injective
    rw [Equiv.symm_apply_apply]
    change (f.map hy k).comp (of (M := L)) = (of (M := M)).comp L.subtype
    exact f.map_comp hy
  rw [← heq]
  exact f.map_injective_of_injective (g := L.subtype) Subtype.val_injective k

end Algebra.GrothendieckAddGroup
