/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.CharacterReconstruction

/-!
# Symmetric restricted-product duality

This file applies character reconstruction to the transposed local
bicharacters.  It constructs the duality equivalence in the opposite direction
and identifies its evaluation with the original pairing, without invoking a
general Pontryagin biduality theorem.
-/

public section

set_option warningAsError true

open Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}
variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]
variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))
variable (e : ∀ i, X i →* Y i →* Circle)

/-- The left annihilator of a subgroup under a multiplicative bicharacter. -/
@[expose] noncomputable def leftAnnihilator {X Y : Type*} [CommGroup X] [CommGroup Y]
    (V : Subgroup Y) (e : X →* Y →* Circle) : Subgroup X :=
  rightAnnihilator V (rightCharacter e)

@[simp]
theorem mem_leftAnnihilator {X Y : Type*} [CommGroup X] [CommGroup Y]
    {V : Subgroup Y} {e : X →* Y →* Circle} {x : X} :
    x ∈ leftAnnihilator V e ↔ ∀ y, y ∈ V → e x y = 1 :=
  Iff.rfl

/-- Orthogonality is preserved when a bicharacter is viewed in the opposite
direction through `rightCharacter`. -/
theorem orthogonal_rightCharacter
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1) :
    ∀ i (y : Y i), y ∈ V i → ∀ x : X i, x ∈ U i → rightCharacter (e i) y x = 1 := by
  intro i y hy x hx
  exact horth i x hx y hy

/-- Transposing every local bicharacter does not change the global pairing's
evaluation. -/
@[simp]
theorem pairing_rightCharacter (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    pairing V U (fun i ↦ rightCharacter (e i)) y x = pairing U V e x y :=
  rfl

variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- Joint continuity is preserved by transposing the two inputs of a local
bicharacter. -/
theorem continuous_rightCharacter
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2) :
    ∀ i, Continuous fun p : Y i × X i ↦ rightCharacter (e i) p.1 p.2 := by
  intro i
  exact (he i).comp (continuous_snd.prodMk continuous_fst)

/-- The symmetric restricted-product duality equivalence, constructed directly
from left local perfectness and the reverse exact-annihilator equality. -/
@[expose] noncomputable def symmetricPontryaginDualEquiv
    [∀ i, Finite (Y i)] [∀ i, DiscreteTopology (Y i)] [∀ i, IsTopologicalGroup (X i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (e i))
    (hU : ∀ i, U i = leftAnnihilator (V i) (e i)) :
    (Πʳ i, [X i, U i]) ≃ₜ* PontryaginDual (Πʳ i, [Y i, V i]) :=
  pontryaginDualEquiv V U (fun i ↦ rightCharacter (e i))
    (orthogonal_rightCharacter U V e horth) hVopen hUopen
    (continuous_rightCharacter e he) hperfect hU

/-- Evaluation of the symmetric equivalence is the original global pairing
with its arguments in their original order. -/
@[simp]
theorem symmetricPontryaginDualEquiv_apply
    [∀ i, Finite (Y i)] [∀ i, DiscreteTopology (Y i)] [∀ i, IsTopologicalGroup (X i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (e i))
    (hU : ∀ i, U i = leftAnnihilator (V i) (e i))
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) :
    symmetricPontryaginDualEquiv U V e horth hUopen hVopen he hperfect hU x y =
      pairing U V e x y :=
  rfl

/-- The original and symmetric restricted-product duality equivalences have
the same evaluation pairing.  This is a direct computation, not an application
of a general biduality equivalence. -/
theorem pontryaginDualEquiv_apply_eq_symmetric
    [∀ i, Finite (X i)] [∀ i, DiscreteTopology (X i)] [∀ i, IsTopologicalGroup (Y i)]
    [∀ i, Finite (Y i)] [∀ i, DiscreteTopology (Y i)] [∀ i, IsTopologicalGroup (X i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfectRight : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i))
    (hperfectLeft : ∀ i, Function.Bijective (e i))
    (hU : ∀ i, U i = leftAnnihilator (V i) (e i))
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) :
    pontryaginDualEquiv U V e horth hUopen hVopen he hperfectRight hV y x =
      symmetricPontryaginDualEquiv U V e horth hUopen hVopen he hperfectLeft hU x y :=
  rfl

end RestrictedProduct
