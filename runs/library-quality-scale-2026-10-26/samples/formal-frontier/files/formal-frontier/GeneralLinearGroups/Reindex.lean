/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Whitehead
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing general linear groups

This file transports a general linear group along an equivalence of finite
index types and proves its elementary coherence and coefficient-naturality
laws.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uκ uτ uR uS

variable {ι : Type uι} {κ : Type uκ} {τ : Type uτ}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reindex a general linear group along an equivalence of finite index types. -/
def reindexEquiv (R : Type uR) [Semiring R] (e : ι ≃ κ) : GL ι R ≃* GL κ R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

/-- Reindexing evaluates a matrix entry at the inverse images of its row and column. -/
@[simp]
theorem reindexEquiv_apply (R : Type uR) [Semiring R] (e : ι ≃ κ)
    (g : GL ι R) (i j : κ) :
    reindexEquiv R e g i j = g (e.symm i) (e.symm j) := rfl

/-- Inverse reindexing evaluates a matrix entry at the images of its row and column. -/
@[simp]
theorem reindexEquiv_symm_apply (R : Type uR) [Semiring R] (e : ι ≃ κ)
    (g : GL κ R) (i j : ι) :
    (reindexEquiv R e).symm g i j = g (e i) (e j) := rfl

/-- The inverse group equivalence is reindexing along the inverse index equivalence. -/
@[simp]
theorem reindexEquiv_symm (R : Type uR) [Semiring R] (e : ι ≃ κ) :
    (reindexEquiv R e).symm = reindexEquiv R e.symm := rfl

/-- Reindexing along the identity index equivalence is the identity group equivalence. -/
@[simp]
theorem reindexEquiv_refl (R : Type uR) [Semiring R] :
    reindexEquiv R (Equiv.refl ι) = MulEquiv.refl (GL ι R) := by
  rfl

/-- Successive reindexings agree with reindexing along the composite index equivalence. -/
@[simp]
theorem reindexEquiv_trans (R : Type uR) [Semiring R]
    [Fintype τ] [DecidableEq τ] (e : ι ≃ κ) (e' : κ ≃ τ) :
    (reindexEquiv R e).trans (reindexEquiv R e') =
      reindexEquiv R (e.trans e') := by
  rfl

/-- Applying a coefficient homomorphism commutes with reindexing the general linear group. -/
@[simp]
theorem mapRingHom_reindexEquiv
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (f : R →+* S) (e : ι ≃ κ) (g : GL ι R) :
    mapRingHom f (reindexEquiv R e g) =
      reindexEquiv S e (mapRingHom f g) := by
  rfl

end Matrix.GeneralLinearGroup
