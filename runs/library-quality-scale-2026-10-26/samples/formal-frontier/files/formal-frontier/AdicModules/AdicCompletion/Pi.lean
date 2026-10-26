/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Finiteness.Ideal
public import AdicModules.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Pi

/-!
# Products and adic completion

The comparison `AdicCompletion.pi` commutes with the maps on completions induced by
componentwise linear maps between dependent products. The square is an equality of
linear maps over the completed ring, for every ideal and arbitrary indexing types.
For a finitely generated ideal, this comparison is an algebraic linear equivalence,
without any finiteness assumption on the indexing type or the modules.

## References

This file uses Mathlib's completion functor and product comparison, formalized by
Judith Ludwig and Christian Merten in
`Mathlib.RingTheory.AdicCompletion.Functoriality`, and Mathlib's dependent-product
linear map and projection API in `Mathlib.LinearAlgebra.Pi`.
-/

@[expose] public section

set_option warningAsError true

universe uR uJ uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} {M : J → Type uM} {N : J → Type uN}
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- The product comparison for adic completion is natural in componentwise linear maps.
This is an equality of linear maps over the completed ring, without finiteness
assumptions on the ideal or indexing type. -/
theorem pi_comp_map (f : ∀ j, M j →ₗ[R] N j) :
    pi I N ∘ₗ map I (LinearMap.piMap f) =
      LinearMap.piMap (fun j ↦ map I (f j)) ∘ₗ pi I M := by
  simp only [pi, LinearMap.piMap, LinearMap.pi_comp, LinearMap.comp_assoc,
    LinearMap.proj_pi, map_comp]

/-- Applying the product comparison after a componentwise map on completions amounts
to applying the induced map to each completed component. -/
@[simp]
theorem pi_map (f : ∀ j, M j →ₗ[R] N j) (x : AdicCompletion I (∀ j, M j)) :
    pi I N (map I (LinearMap.piMap f) x) =
      fun j ↦ map I (f j) (pi I M x j) :=
  LinearMap.congr_fun (pi_comp_map I f) x

variable (M)

/-- For a finitely generated ideal, adic completion commutes algebraically with
arbitrary products. -/
theorem pi_bijective_of_fg (hI : I.FG) : Function.Bijective (pi I M) := by
  let e (n : ℕ) := (hI.pow (n := n)).quotientPi M
  have he (n : ℕ)
      (z : (∀ j, M j) ⧸ (I ^ n • ⊤ : Submodule R (∀ j, M j))) (j : J) :
      e n z j = (LinearMap.proj j).reduceModIdeal (I ^ n) z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
      exact (congrFun ((hI.pow (n := n)).quotientPi_apply_mk M z) j).trans
        (LinearMap.reduceModIdeal_apply (I ^ n) (LinearMap.proj j) z).symm
  have ht {m n : ℕ} (hmn : m ≤ n)
      (z : (∀ j, M j) ⧸ (I ^ n • ⊤ : Submodule R (∀ j, M j))) :
      e m (transitionMap I (∀ j, M j) hmn z) =
        fun j ↦ transitionMap I (M j) hmn (e n z j) := by
    funext j
    rw [he, he]
    exact (LinearMap.congr_fun
      (transitionMap_comp_reduceModIdeal I (LinearMap.proj j) hmn) z).symm
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    apply (e n).injective
    funext j
    rw [he, he]
    exact congrArg (fun z : ∀ j, AdicCompletion I (M j) ↦ (z j).val n) h
  · intro y
    refine ⟨⟨fun n ↦ (e n).symm (fun j ↦ (y j).val n), ?_⟩, ?_⟩
    · intro m n hmn
      apply (e m).injective
      rw [ht, (e m).apply_symm_apply]
      funext j
      rw [(e n).apply_symm_apply]
      exact (y j).property hmn
    · funext j
      apply Subtype.ext
      funext n
      change (LinearMap.proj j).reduceModIdeal (I ^ n)
        ((e n).symm (fun j ↦ (y j).val n)) = (y j).val n
      rw [← he, (e n).apply_symm_apply]

/-- The algebraic product comparison for completion at a finitely generated ideal.
Its forward map is the existing `AdicCompletion.pi`. -/
noncomputable def piEquivOfFG (hI : I.FG) :
    AdicCompletion I (∀ j, M j) ≃ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  LinearEquiv.ofBijective (pi I M) (pi_bijective_of_fg I M hI)

@[simp]
theorem piEquivOfFG_toLinearMap (hI : I.FG) :
    (piEquivOfFG I M hI).toLinearMap = pi I M :=
  rfl

end AdicCompletion

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} (M : J → Type uM)
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

/-- The product equivalence has the canonical product comparison as its forward map. -/
@[simp]
theorem piEquivOfFG_apply (hI : I.FG) (x : AdicCompletion I (∀ j, M j)) :
    piEquivOfFG I M hI x = pi I M x :=
  LinearMap.congr_fun (piEquivOfFG_toLinearMap I M hI) x

/-- Each coordinate of the product equivalence is induced by the corresponding projection. -/
@[simp]
theorem piEquivOfFG_apply_apply (hI : I.FG)
    (x : AdicCompletion I (∀ j, M j)) (j : J) :
    piEquivOfFG I M hI x j = map I (LinearMap.proj j) x :=
  congrFun (piEquivOfFG_apply I M hI x) j

/-- Projecting the inverse product equivalence recovers the given completed coordinate. -/
@[simp]
theorem map_proj_piEquivOfFG_symm (hI : I.FG)
    (x : ∀ j, AdicCompletion I (M j)) (j : J) :
    map I (LinearMap.proj j) ((piEquivOfFG I M hI).symm x) = x j := by
  simpa only [piEquivOfFG_apply_apply] using
    congrFun ((piEquivOfFG I M hI).apply_symm_apply x) j

/-- The product equivalence sends the image of a product to the images of its coordinates. -/
@[simp]
theorem piEquivOfFG_of (hI : I.FG) (x : ∀ j, M j) :
    piEquivOfFG I M hI (of I (∀ j, M j) x) = fun j ↦ of I (M j) (x j) := by
  funext j
  simpa only [piEquivOfFG_apply_apply, LinearMap.proj_apply] using
    (map_of I (LinearMap.proj j) x)

/-- The inverse product equivalence respects the canonical maps into completion. -/
@[simp]
theorem piEquivOfFG_symm_of (hI : I.FG) (x : ∀ j, M j) :
    (piEquivOfFG I M hI).symm (fun j ↦ of I (M j) (x j)) =
      of I (∀ j, M j) x := by
  apply (piEquivOfFG I M hI).injective
  simp only [LinearEquiv.apply_symm_apply, piEquivOfFG_of]

/-- On finite products, the finitely generated ideal construction agrees with the finite
product equivalence, whose construction does not require finite generation. -/
theorem piEquivOfFG_eq_piEquivOfFintype [DecidableEq J] [Fintype J] (hI : I.FG) :
    piEquivOfFG I M hI = piEquivOfFintype I M := by
  apply LinearEquiv.ext
  intro x
  simp only [piEquivOfFG_apply, piEquivOfFintype_apply]

variable {M} {N : J → Type uN}
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- The inverse product equivalence commutes with componentwise maps on completions. -/
@[simp]
theorem piEquivOfFG_symm_map (hI : I.FG) (f : ∀ j, M j →ₗ[R] N j)
    (x : ∀ j, AdicCompletion I (M j)) :
    (piEquivOfFG I N hI).symm (fun j ↦ map I (f j) (x j)) =
      map I (LinearMap.piMap f) ((piEquivOfFG I M hI).symm x) := by
  apply (piEquivOfFG I N hI).injective
  rw [LinearEquiv.apply_symm_apply, piEquivOfFG_apply, pi_map,
    ← piEquivOfFG_apply I M hI, LinearEquiv.apply_symm_apply]

end AdicCompletion
