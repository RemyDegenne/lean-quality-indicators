/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.RightExtension
public import ProjectiveModules.Module.RightExtensionQuotient
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite residue modules for right-module extension

This file specializes the linear-equivalence and binary-product
constructions from `ModuleCat.RightExtension` to quotients by the action of a
two-sided ideal, using `ModuleCat.RightExtension.idealQuotientLinearEquiv`. It
also gives finite-generation and dimension consequences over a division-ring
quotient.
-/

@[expose] public section

universe uR uS uM uN

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)
variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

section IdealQuotient

variable {R : Type uR} [Ring R]
variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- A right-linear equivalence descends to the quotients by the action of a
two-sided ideal. -/
def idealQuotientMapLinearEquiv (I : Ideal R) [I.IsTwoSided]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    IdealQuotient (M := M) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      IdealQuotient (M := N) I :=
  (idealQuotientLinearEquiv (M := M) I).symm.trans <|
    (mapLinearEquiv (Ideal.Quotient.mk I) e).trans <|
      idealQuotientLinearEquiv (M := N) I

@[simp]
theorem idealQuotientMapLinearEquiv_mk (I : Ideal R) [I.IsTwoSided]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) (m : M) :
    idealQuotientMapLinearEquiv I e
        (Submodule.Quotient.mk (p := idealSubmodule (M := M) I) m) =
      Submodule.Quotient.mk (p := idealSubmodule (M := N) I) (e m) := by
  simp [idealQuotientMapLinearEquiv]

/-- Quotienting a product of right modules by the action of a two-sided ideal
is the product of the corresponding quotient modules. -/
def idealQuotientProdLinearEquiv (I : Ideal R) [I.IsTwoSided] :
    IdealQuotient (M := M × N) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      IdealQuotient (M := M) I × IdealQuotient (M := N) I :=
  (idealQuotientLinearEquiv (M := M × N) I).symm.trans <|
    (prodLinearEquiv (f := Ideal.Quotient.mk I) (M := M) (N := N)).trans <|
      (idealQuotientLinearEquiv (M := M) I).prodCongr
        (idealQuotientLinearEquiv (M := N) I)

@[simp]
theorem idealQuotientProdLinearEquiv_mk (I : Ideal R) [I.IsTwoSided]
    (m : M) (n : N) :
    idealQuotientProdLinearEquiv (M := M) (N := N) I
        (Submodule.Quotient.mk
          (p := idealSubmodule (M := M × N) I) (m, n)) =
      (Submodule.Quotient.mk (p := idealSubmodule (M := M) I) m,
        Submodule.Quotient.mk (p := idealSubmodule (M := N) I) n) := by
  simp [idealQuotientProdLinearEquiv]

/-- A finitely generated right module has a finitely generated quotient by
the action of a two-sided ideal. -/
instance idealQuotientFinite (I : Ideal R) [I.IsTwoSided]
    [Module.Finite Rᵐᵒᵖ M] :
    Module.Finite (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) :=
  Module.Finite.equiv (idealQuotientLinearEquiv (M := M) I)

/-- Freeness of the extension of scalars transfers to the quotient by the
action of a two-sided ideal. -/
theorem idealQuotientFree (I : Ideal R) [I.IsTwoSided]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M)] :
    Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) :=
  Module.Free.of_equiv (idealQuotientLinearEquiv (M := M) I)

/-- The quotient of a right module by the action of a two-sided maximal ideal
is free over the resulting division ring. -/
theorem idealQuotientFree_of_isMaximal (I : Ideal R) [I.IsTwoSided]
    [I.IsMaximal] :
    Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) := by
  let _ := Ideal.Quotient.divisionRing I
  let _ : Module.Free (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M) :=
    Module.Free.of_divisionRing (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M)
  exact idealQuotientFree I

/-- The dimension of the quotient of a product is the sum of the dimensions
of the two quotient modules whenever dimension is available over the quotient
scalar ring. -/
theorem finrank_idealQuotient_prod (I : Ideal R) [I.IsTwoSided]
    [StrongRankCondition (R ⧸ I)ᵐᵒᵖ]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I)]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I)]
    [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] :
    Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M × N) I) =
      Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) +
        Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I) := by
  rw [(idealQuotientProdLinearEquiv (M := M) (N := N) I).finrank_eq,
    Module.finrank_prod]

/-- Modulo a two-sided maximal ideal, the dimension of the quotient of a product
is the sum of the dimensions of the two quotient modules. -/
theorem finrank_idealQuotient_prod_of_isMaximal
    (I : Ideal R) [I.IsTwoSided] [I.IsMaximal]
    [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] :
    Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M × N) I) =
      Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) +
        Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I) := by
  let _ := Ideal.Quotient.divisionRing I
  let _ := idealQuotientFree_of_isMaximal (M := M) I
  let _ := idealQuotientFree_of_isMaximal (M := N) I
  let _ : StrongRankCondition (R ⧸ I)ᵐᵒᵖ :=
    IsNoetherianRing.strongRankCondition (R ⧸ I)ᵐᵒᵖ
  exact finrank_idealQuotient_prod I

end IdealQuotient

end ModuleCat.RightExtension
