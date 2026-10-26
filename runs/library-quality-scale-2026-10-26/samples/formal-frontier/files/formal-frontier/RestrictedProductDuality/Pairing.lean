/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Pairings of restricted products

This file constructs the algebraic pairing induced by a family of bicharacters which annihilate
the distinguished subgroups. The global value is a `finprod`; orthogonality proves that its
multiplicative support is finite.
-/

public section

set_option warningAsError true

open Filter Function Set
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}
variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]
variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))
variable (e : ∀ i, X i →* Y i →* Circle)

/-- Orthogonality of the distinguished subgroups makes every restricted-product evaluation
family finitely supported. -/
theorem pairing_hasFiniteMulSupport
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) :
    HasFiniteMulSupport (fun i ↦ e i (x i) (y i)) := by
  exact Filter.eventually_cofinite.mp <|
    (x.2.and y.2).mono fun i hi ↦ horth i (x i) hi.1 (y i) hi.2

/-- The product pairing induced on two cofinite restricted products.

The `finprod` agrees with the ordinary product over any finite set containing all coordinates
where the local factor is not `1`. -/
@[expose] noncomputable def pairing
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) : Circle :=
  ∏ᶠ i, e i (x i) (y i)

/-- Evaluation is the ordinary product over any finite set outside which all local factors are
`1`. In particular, its value is independent of a chosen finite exceptional presentation. -/
theorem pairing_eq_prod (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) (s : Finset ι)
    (hs : ∀ i, i ∉ s → e i (x i) (y i) = 1) :
    pairing U V e x y = ∏ i ∈ s, e i (x i) (y i) := by
  rw [pairing]
  apply finprod_eq_prod_of_mulSupport_subset
  intro i hi
  by_contra his
  exact (mem_mulSupport.mp hi) (hs i his)

open scoped Classical in
@[simp]
theorem pairing_mulSingle_left (i : ι) (x : X i) (y : Πʳ i, [Y i, V i]) :
    pairing U V e (mulSingle U i x) y = e i x (y i) := by
  classical
  rw [pairing_eq_prod (s := {i})]
  · simp
  · intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [mulSingle_eq_of_ne U x hji]

open scoped Classical in
@[simp]
theorem pairing_mulSingle_right (x : Πʳ i, [X i, U i]) (i : ι) (y : Y i) :
    pairing U V e x (mulSingle V i y) = e i (x i) y := by
  classical
  rw [pairing_eq_prod (s := {i})]
  · simp
  · intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [mulSingle_eq_of_ne V y hji]

@[simp]
theorem pairing_one_left
    (y : Πʳ i, [Y i, V i]) : pairing U V e 1 y = 1 := by
  simp [pairing]

@[simp]
theorem pairing_one_right
    (x : Πʳ i, [X i, U i]) : pairing U V e x 1 = 1 := by
  simp [pairing]

theorem pairing_mul_left
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (x x' : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) :
    pairing U V e (x * x') y = pairing U V e x y * pairing U V e x' y := by
  simp only [pairing, RestrictedProduct.mul_apply, map_mul]
  exact finprod_mul_distrib (pairing_hasFiniteMulSupport U V e horth x y)
    (pairing_hasFiniteMulSupport U V e horth x' y)

theorem pairing_mul_right
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (x : Πʳ i, [X i, U i]) (y y' : Πʳ i, [Y i, V i]) :
    pairing U V e x (y * y') = pairing U V e x y * pairing U V e x y' := by
  simp only [pairing, RestrictedProduct.mul_apply, map_mul]
  exact finprod_mul_distrib (pairing_hasFiniteMulSupport U V e horth x y)
    (pairing_hasFiniteMulSupport U V e horth x y')

/-- The character of the first restricted product determined by an element of the second one. -/
@[expose] noncomputable def pairingMonoidHom
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (y : Πʳ i, [Y i, V i]) : (Πʳ i, [X i, U i]) →* Circle where
  toFun x := pairing U V e x y
  map_one' := pairing_one_left U V e y
  map_mul' x x' := pairing_mul_left U V e horth x x' y

@[simp]
theorem pairingMonoidHom_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    pairingMonoidHom U V e horth y x = pairing U V e x y :=
  rfl

/-- The global pairing, bundled as a homomorphism into the algebraic character group. -/
@[expose] noncomputable def pairingHom
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1) :
    (Πʳ i, [Y i, V i]) →* ((Πʳ i, [X i, U i]) →* Circle) where
  toFun := pairingMonoidHom U V e horth
  map_one' := MonoidHom.ext fun x ↦ pairing_one_right U V e x
  map_mul' y y' := MonoidHom.ext fun x ↦ pairing_mul_right U V e horth x y y'

@[simp]
theorem pairingHom_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    pairingHom U V e horth y x = pairing U V e x y :=
  rfl

end RestrictedProduct
