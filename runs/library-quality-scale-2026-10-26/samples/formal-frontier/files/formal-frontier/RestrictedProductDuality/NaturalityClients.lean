/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Naturality
public import RestrictedProductDuality.Clients

/-!
# Naturality clients

These examples exercise the public naturality square for arbitrary index
universes, including a genuinely infinite index and a nontrivial finite cyclic
coordinate group.
-/

public section

set_option warningAsError true

noncomputable section

open Set
open scoped RestrictedProduct

namespace RestrictedProduct

universe u

/-- The discrete topology for cyclic naturality clients, scoped to this file. -/
local instance zmodTwoTopologicalSpaceNaturality :
    TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
/-- The corresponding discrete-topology witness for cyclic naturality clients. -/
local instance zmodTwoDiscreteTopologyNaturality :
    DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

private abbrev Z2 := Multiplicative (ZMod 2)

private def zmodTwoId : Z2 →ₜ* Z2 :=
  ContinuousMonoidHom.mk (MonoidHom.id Z2) continuous_id

private def zmodBot (ι : Type u) : ι → Subgroup Z2 := fun _ ↦ ⊥
private def zmodTop (ι : Type u) : ι → Subgroup Z2 := fun _ ↦ ⊤
private def zmodPairing (ι : Type u) : ι → Z2 →* Z2 →* Circle :=
  fun _ ↦ zmodBicharacter 2
private def zmodIdFamily (ι : Type u) : ι → Z2 →ₜ* Z2 := fun _ ↦ zmodTwoId

private def zmodTwoSquare : Z2 →ₜ* Z2 :=
  ContinuousMonoidHom.mk (powMonoidHom 2) continuous_of_discreteTopology

private def zmodSquareFamily (ι : Type u) : ι → Z2 →ₜ* Z2 :=
  fun _ ↦ zmodTwoSquare

private def zmodRestrictedSquareBot (ι : Type u) :
    (Πʳ i, [Z2, zmodBot ι i]) →ₜ* (Πʳ i, [Z2, zmodBot ι i]) :=
  mapContinuousMonoidHom (zmodBot ι) (zmodBot ι) (zmodSquareFamily ι)
    (Filter.Eventually.of_forall fun i x hx ↦ by
      rw [show x = 1 by simpa [zmodBot] using hx]
      simp [zmodSquareFamily])

private def zmodRestrictedSquareTop (ι : Type u) :
    (Πʳ i, [Z2, zmodTop ι i]) →ₜ* (Πʳ i, [Z2, zmodTop ι i]) :=
  mapContinuousMonoidHom (zmodTop ι) (zmodTop ι) (zmodSquareFamily ι)
    (Filter.Eventually.of_forall fun i x _hx ↦ by simp [zmodTop])

/-- The naturality square specializes to the identity maps over every index
type, with nontrivial cyclic local pairings. -/
private theorem naturality_identity_arbitraryIndex (ι : Type u) :
    (toPontryaginDual (zmodBot ι) (zmodTop ι) (zmodPairing ι)
      (by
        intro i x hx y _hy
        have : x = 1 := by simpa [zmodBot] using hx
        subst x
        simp [zmodPairing])
      (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
      (fun _ ↦ continuous_of_discreteTopology)).comp
        (mapContinuousMonoidHom (zmodTop ι) (zmodTop ι) (zmodIdFamily ι)
          (Filter.Eventually.of_forall fun i x _hx ↦ by
            simp [zmodIdFamily, zmodTwoId, zmodTop])) =
      (PontryaginDual.map
        (mapContinuousMonoidHom (zmodBot ι) (zmodBot ι) (zmodIdFamily ι)
          (Filter.Eventually.of_forall fun i x hx ↦ by
            change x = 1
            simpa [zmodBot] using hx))).comp
        (toPontryaginDual (zmodBot ι) (zmodTop ι) (zmodPairing ι)
          (by
            intro i x hx y _hy
            have : x = 1 := by simpa [zmodBot] using hx
            subst x
            simp [zmodPairing])
          (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
          (fun _ ↦ continuous_of_discreteTopology)) := by
  apply toPontryaginDual_natural
  intro i x y
  rfl

/-- A genuinely infinite-index specialization. -/
private theorem naturality_identity_infiniteIndex :
    (toPontryaginDual (zmodBot ℕ) (zmodTop ℕ) (zmodPairing ℕ)
      (by
        intro i x hx y _hy
        have : x = 1 := by simpa [zmodBot] using hx
        subst x
        simp [zmodPairing])
      (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
      (fun _ ↦ continuous_of_discreteTopology)).comp
        (mapContinuousMonoidHom (zmodTop ℕ) (zmodTop ℕ) (zmodIdFamily ℕ)
          (Filter.Eventually.of_forall fun i x _hx ↦ by
            simp [zmodIdFamily, zmodTwoId, zmodTop])) =
      (PontryaginDual.map
        (mapContinuousMonoidHom (zmodBot ℕ) (zmodBot ℕ) (zmodIdFamily ℕ)
          (Filter.Eventually.of_forall fun i x hx ↦ by
            change x = 1
            simpa [zmodBot] using hx))).comp
        (toPontryaginDual (zmodBot ℕ) (zmodTop ℕ) (zmodPairing ℕ)
          (by
            intro i x hx y _hy
            have : x = 1 := by simpa [zmodBot] using hx
            subst x
            simp [zmodPairing])
          (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
          (fun _ ↦ continuous_of_discreteTopology)) := by
  apply toPontryaginDual_natural
  intro i x y
  rfl

/-- Squaring is a non-identity endomorphism of the multiplicative `ZMod 2`. -/
private theorem zmodTwoSquare_nonidentity :
    zmodTwoSquare (Multiplicative.ofAdd 1) ≠ Multiplicative.ofAdd 1 := by
  decide

/-- Squaring in either coordinate of the standard `ZMod 2` bicharacter gives
adjoint coordinate maps. -/
private theorem zmodTwoSquare_adjoint (x y : Z2) :
    zmodBicharacter 2 x (zmodTwoSquare y) =
      zmodBicharacter 2 (zmodTwoSquare x) y := by
  rw [show zmodTwoSquare y = y ^ 2 by rfl, show zmodTwoSquare x = x ^ 2 by rfl]
  simp only [map_pow, MonoidHom.pow_apply]

/-- The non-identity coordinate map induces maps on both genuinely
infinite-index restricted products used by the naturality square. -/
private noncomputable def zmodTwoSquare_restrictedMaps :
    ((Πʳ i : ℕ, [Z2, zmodBot ℕ i]) →ₜ* (Πʳ i : ℕ, [Z2, zmodBot ℕ i])) ×
      ((Πʳ i : ℕ, [Z2, zmodTop ℕ i]) →ₜ* (Πʳ i : ℕ, [Z2, zmodTop ℕ i])) :=
  (zmodRestrictedSquareBot ℕ, zmodRestrictedSquareTop ℕ)

/-- The nonidentity squaring maps satisfy the full infinite-index naturality square. -/
private theorem naturality_square_infiniteIndex :
    (toPontryaginDual (zmodBot ℕ) (zmodTop ℕ) (zmodPairing ℕ)
      (by
        intro i x hx y _hy
        have : x = 1 := by simpa [zmodBot] using hx
        subst x
        simp [zmodPairing])
      (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
      (fun _ ↦ continuous_of_discreteTopology)).comp (zmodRestrictedSquareTop ℕ) =
    (PontryaginDual.map (zmodRestrictedSquareBot ℕ)).comp
      (toPontryaginDual (zmodBot ℕ) (zmodTop ℕ) (zmodPairing ℕ)
        (by
          intro i x hx y _hy
          have : x = 1 := by simpa [zmodBot] using hx
          subst x
          simp [zmodPairing])
        (fun _ ↦ isOpen_discrete _) (fun _ ↦ isOpen_discrete _)
        (fun _ ↦ continuous_of_discreteTopology)) := by
  apply toPontryaginDual_natural
  intro i x y
  change zmodBicharacter 2 x (zmodTwoSquare y) =
    zmodBicharacter 2 (zmodTwoSquare x) y
  exact zmodTwoSquare_adjoint x y

end RestrictedProduct
