/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Quotient conjugation on a kernel abelianization

For an abstract group extension `1 → N → E → Q → 1`, conjugation by
`E` acts on `N`.  Embedded elements of `N` act by inner automorphisms, hence
trivially on `Abelianization N`.  This file descends the abelianized action to
the quotient group `Q`.

The principal construction is
`GroupExtension.quotientConjActAbelianization`.  Its lift formula fixes the
orientation: a lift `e : E` of `q : Q` sends the class of `n : N` to the class
of `S.conjAct e n`, where mathlib's `conjAct` is conjugation by `e` on the left.
The public lift-independence lemmas make the quotient descent inspectable.

This algebraic quotient action is the precursor to the topological
quotient-conjugation action. It introduces no topology, coinvariants,
or (co)homology. Pinned mathlib's `GroupExtension.Equiv` fixes
the kernel and quotient while varying the middle group, so the final lemmas
give naturality under exactly that strongest existing small structured notion.
A kernel- or quotient-changing compatibility theorem awaits a corresponding
structured extension-morphism API.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uN uE uQ

namespace GroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]

/-- The conjugation action of the middle group on the abelianization of the
kernel of a group extension. -/
def conjActAbelianization (S : GroupExtension N E Q) :
    E →* MulAut (Abelianization N) where
  toFun e := (S.conjAct e).abelianizationCongr
  map_one' := by
    rw [map_one]
    exact abelianizationCongr_refl
  map_mul' e e' := by
    apply MulEquiv.toMonoidHom_injective
    apply Abelianization.hom_ext
    ext n
    change Abelianization.of (S.conjAct (e * e') n) =
      Abelianization.of (S.conjAct e (S.conjAct e' n))
    rw [map_mul]
    rfl

/-- Abelianized conjugation sends the class of a kernel element to the class
of its conjugate. -/
@[simp]
theorem conjActAbelianization_apply_of (S : GroupExtension N E Q) (e : E) (n : N) :
    S.conjActAbelianization e (Abelianization.of n) =
      Abelianization.of (S.conjAct e n) := rfl

/-- An embedded kernel element acts trivially on the kernel abelianization. -/
@[simp]
theorem conjActAbelianization_inl (S : GroupExtension N E Q) (n : N) :
    S.conjActAbelianization (S.inl n) = 1 := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext x
  change Abelianization.of (S.conjAct (S.inl n) x) = Abelianization.of x
  have h : S.conjAct (S.inl n) x = n * x * n⁻¹ := by
    apply S.inl_injective
    rw [S.inl_conjAct_comm]
    simp
  rw [h]
  simp

/-- The kernel of the extension projection acts trivially after abelianizing
the kernel. -/
theorem ker_rightHom_le_ker_conjActAbelianization
    (S : GroupExtension N E Q) :
    S.rightHom.ker ≤ S.conjActAbelianization.ker := by
  rw [← S.range_inl_eq_ker_rightHom]
  rintro e ⟨n, rfl⟩
  rw [MonoidHom.mem_ker]
  exact S.conjActAbelianization_inl n

/-- The quotient group acts canonically on the abelianization of the kernel by
conjugation through any lift to the middle group. -/
noncomputable def quotientConjActAbelianization (S : GroupExtension N E Q) :
    Q →* MulAut (Abelianization N) :=
  (QuotientGroup.lift S.rightHom.ker S.conjActAbelianization
    (ker_rightHom_le_ker_conjActAbelianization S)).comp
      S.quotientKerRightHomEquivRight.symm.toMonoidHom

/-- Characterization of the quotient action on an arbitrary lift. -/
@[simp]
theorem quotientConjActAbelianization_rightHom (S : GroupExtension N E Q) (e : E) :
    S.quotientConjActAbelianization (S.rightHom e) =
      S.conjActAbelianization e := by
  change QuotientGroup.lift S.rightHom.ker S.conjActAbelianization
    (ker_rightHom_le_ker_conjActAbelianization S)
      (S.quotientKerRightHomEquivRight.symm (S.rightHom e)) = _
  have hq : S.quotientKerRightHomEquivRight.symm (S.rightHom e) =
      QuotientGroup.mk' S.rightHom.ker e := by
    apply S.quotientKerRightHomEquivRight.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hq]
  exact QuotientGroup.lift_mk' S.rightHom.ker
    (ker_rightHom_le_ker_conjActAbelianization S) e

/-- Pointwise lift formula for the quotient action, including its conjugation
orientation on representatives of the kernel abelianization. -/
@[simp]
theorem quotientConjActAbelianization_apply_of (S : GroupExtension N E Q)
    (e : E) (n : N) :
    S.quotientConjActAbelianization (S.rightHom e) (Abelianization.of n) =
      Abelianization.of (S.conjAct e n) := by
  rw [S.quotientConjActAbelianization_rightHom]
  rfl

/-- Two lifts of the same quotient element induce the same automorphism of the
kernel abelianization. -/
theorem conjActAbelianization_eq_of_rightHom_eq (S : GroupExtension N E Q)
    {e e' : E} (h : S.rightHom e = S.rightHom e') :
    S.conjActAbelianization e = S.conjActAbelianization e' := by
  rw [← S.quotientConjActAbelianization_rightHom e,
    ← S.quotientConjActAbelianization_rightHom e', h]

/-- Inspectable representative-level form of independence from the chosen
lift of a quotient element. -/
theorem abelianization_conjAct_eq_of_rightHom_eq (S : GroupExtension N E Q)
    {e e' : E} (h : S.rightHom e = S.rightHom e') (n : N) :
    Abelianization.of (S.conjAct e n) = Abelianization.of (S.conjAct e' n) := by
  rw [← S.conjActAbelianization_apply_of,
    ← S.conjActAbelianization_apply_of,
    S.conjActAbelianization_eq_of_rightHom_eq h]

namespace Equiv

variable {E' : Type*} [Group E'] {S : GroupExtension N E Q}
  {S' : GroupExtension N E' Q}

/-- An equivalence of extensions intertwines the middle-group actions on the
common kernel abelianization. -/
theorem conjActAbelianization (equiv : S.Equiv S') (e : E) :
    S'.conjActAbelianization (equiv e) = S.conjActAbelianization e := by
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  ext n
  change Abelianization.of (S'.conjAct (equiv e) n) =
    Abelianization.of (S.conjAct e n)
  congr 1
  apply S'.inl_injective
  calc
    S'.inl (S'.conjAct (equiv e) n) =
        equiv e * S'.inl n * (equiv e)⁻¹ := S'.inl_conjAct_comm
    _ = equiv (e * S.inl n * e⁻¹) := by simp
    _ = equiv (S.inl (S.conjAct e n)) :=
      congrArg equiv S.inl_conjAct_comm.symm
    _ = S'.inl (S.conjAct e n) := equiv.map_inl _

/-- Equivalent extensions with the same kernel and quotient have exactly the
same descended action on the kernel abelianization. -/
theorem quotientConjActAbelianization (equiv : S.Equiv S') :
    S'.quotientConjActAbelianization = S.quotientConjActAbelianization := by
  apply MonoidHom.ext
  intro q
  obtain ⟨e, rfl⟩ := S.rightHom_surjective q
  calc
    S'.quotientConjActAbelianization (S.rightHom e) =
        S'.quotientConjActAbelianization (S'.rightHom (equiv e)) :=
      congrArg S'.quotientConjActAbelianization (equiv.rightHom_map e).symm
    _ = S'.conjActAbelianization (equiv e) :=
      S'.quotientConjActAbelianization_rightHom _
    _ = S.conjActAbelianization e := equiv.conjActAbelianization e
    _ = S.quotientConjActAbelianization (S.rightHom e) :=
      (S.quotientConjActAbelianization_rightHom e).symm

end Equiv

end GroupExtension
