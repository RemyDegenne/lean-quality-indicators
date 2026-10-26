/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

/-!
# Selected components of a nonnegatively graded ring

For any natural number `n`, the selected-component Veronese ring is the direct
sum of the whole components in degrees `n * j`. Its canonical ring map into the
original ring has the subring of finite selected-component sums as its range.
The inclusion is injective, and the degree-zero map is an equivalence, when
`0 < n`.
-/

noncomputable section

namespace GradedRing.Veronese

open DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The selected graded ring, retaining precisely the complete components `𝒮 (n * j)`. -/
abbrev VeroneseRing (n : ℕ) := ⨁ (j : ℕ), 𝒮 (n * j)

instance selectedGradedMonoid (n : ℕ) : SetLike.GradedMonoid (fun j : ℕ => 𝒮 (n * j)) where
  one_mem := by simpa using SetLike.one_mem_graded 𝒮
  mul_mem i j x y hx hy := by
    simpa [mul_add] using (SetLike.GradedMul.mul_mem hx hy :
      x * y ∈ 𝒮 (n * i + n * j))

instance instCommRing (n : ℕ) : CommRing (VeroneseRing 𝒮 n) :=
  inferInstanceAs (CommRing (⨁ (j : ℕ), 𝒮 (n * j)))

/-- The canonical inclusion of the selected components into the original ring. -/
def inclusion (n : ℕ) : VeroneseRing 𝒮 n →+* S :=
  DirectSum.coeRingHom (fun j : ℕ => 𝒮 (n * j))

@[simp] theorem inclusion_of (n j : ℕ) (a : 𝒮 (n * j)) :
    inclusion 𝒮 n (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a) = a :=
  DirectSum.coeRingHom_of _ _ _

/-- The `j`th internal component, represented by a single selected summand. -/
def component (n j : ℕ) : AddSubgroup (VeroneseRing 𝒮 n) :=
  AddSubgroup.map (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j) ⊤

theorem mem_component_iff (n j : ℕ) (x : VeroneseRing 𝒮 n) :
    x ∈ component 𝒮 n j ↔ ∃ a : 𝒮 (n * j),
      DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a = x := by
  constructor
  · rintro ⟨a, -, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, trivial, ha⟩

/-- The inclusion maps a new degree `j` into the whole old degree `n*j`. -/
theorem inclusion_mem {n j : ℕ} {x : VeroneseRing 𝒮 n} (hx : x ∈ component 𝒮 n j) :
    inclusion 𝒮 n x ∈ 𝒮 (n * j) := by
  obtain ⟨a, rfl⟩ := (mem_component_iff 𝒮 n j x).mp hx
  rw [inclusion_of]
  exact a.property

/-- Every element in the selected old component comes from the corresponding new component. -/
theorem exists_component (n j : ℕ) (a : 𝒮 (n * j)) :
    ∃ x : VeroneseRing 𝒮 n, x ∈ component 𝒮 n j ∧ inclusion 𝒮 n x = a := by
  refine ⟨DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a, ?_, inclusion_of 𝒮 n j a⟩
  exact (mem_component_iff 𝒮 n j _).mpr ⟨a, rfl⟩

def toComponent (n j : ℕ) : 𝒮 (n * j) →+ component 𝒮 n j where
  toFun a := ⟨DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a,
    (mem_component_iff 𝒮 n j _).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j))
  map_add' a b := Subtype.ext (map_add (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j) a b)

def toComponents (n : ℕ) :
    VeroneseRing 𝒮 n →+ ⨁ (j : ℕ), component 𝒮 n j :=
  DirectSum.map (toComponent 𝒮 n)

theorem toComponents_left (n : ℕ) (x : VeroneseRing 𝒮 n) :
    DirectSum.coeAddMonoidHom (component 𝒮 n) (toComponents 𝒮 n x) = x := by
  induction x using DirectSum.induction_on with
  | zero =>
    change (DirectSum.coeAddMonoidHom (component 𝒮 n)) (toComponents 𝒮 n 0) = 0
    rw [map_zero, map_zero]
  | of j a =>
    change (DirectSum.coeAddMonoidHom (component 𝒮 n))
      ((DirectSum.map (toComponent 𝒮 n)) (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a)) =
        DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    change ((toComponent 𝒮 n j) a).val = _
    rfl
  | add x y hx hy =>
    change _ = x + y
    simp only [map_add, hx, hy]

theorem toComponents_right (n : ℕ) (x : ⨁ (j : ℕ), component 𝒮 n j) :
    toComponents 𝒮 n (DirectSum.coeAddMonoidHom (component 𝒮 n) x) = x := by
  induction x using DirectSum.induction_on with
  | zero =>
    change toComponents 𝒮 n ((DirectSum.coeAddMonoidHom (component 𝒮 n)) 0) = 0
    rw [map_zero, map_zero]
  | of j a =>
    obtain ⟨b, hb⟩ := (mem_component_iff 𝒮 n j a).mp a.property
    rw [DirectSum.coeAddMonoidHom_of]
    change (DirectSum.map (toComponent 𝒮 n)) (a : VeroneseRing 𝒮 n) =
      DirectSum.of (fun k : ℕ => component 𝒮 n k) j a
    rw [← hb, DirectSum.map_of]
    change DirectSum.of (fun k : ℕ => component 𝒮 n k) j ((toComponent 𝒮 n j) b) = _
    congr 1
    apply Subtype.ext
    exact hb
  | add x y hx hy =>
    change _ = x + y
    simp only [map_add, hx, hy]

/-- The selected summands form an internal nonnegative grading. -/
instance instGradedRing (n : ℕ) : GradedRing (component 𝒮 n) where
  one_mem := by
    apply (mem_component_iff 𝒮 n 0 _).mpr
    refine ⟨⟨1, by simpa only [mul_zero] using SetLike.one_mem_graded 𝒮⟩, ?_⟩
    change DirectSum.of (fun k : ℕ => 𝒮 (n * k)) 0 _ =
      (1 : ⨁ (k : ℕ), 𝒮 (n * k))
    rfl
  mul_mem i j a b ha hb := by
    obtain ⟨a', rfl⟩ := (mem_component_iff 𝒮 n i a).mp ha
    obtain ⟨b', rfl⟩ := (mem_component_iff 𝒮 n j b).mp hb
    apply (mem_component_iff 𝒮 n (i + j) _).mpr
    exact ⟨⟨a' * b', by
      simpa only [mul_add] using (SetLike.GradedMul.mul_mem a'.property b'.property :
        (a' : S) * b' ∈ 𝒮 (n * i + n * j))⟩, by
          have hmul := (DirectSum.of_mul_of (A := fun k : ℕ => 𝒮 (n * k)) a' b').symm
          convert hmul using 1⟩
  decompose' := toComponents 𝒮 n
  left_inv := toComponents_left 𝒮 n
  right_inv := toComponents_right 𝒮 n

def reindex (n : ℕ) : VeroneseRing 𝒮 n →+ ⨁ (i : ℕ), 𝒮 i :=
  DirectSum.toAddMonoid fun j => DirectSum.of (fun i : ℕ => 𝒮 i) (n * j)

theorem decompose_inclusion (n : ℕ) (x : VeroneseRing 𝒮 n) :
    DirectSum.decompose 𝒮 (inclusion 𝒮 n x) = reindex 𝒮 n x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j a =>
    change DirectSum.decompose 𝒮 (inclusion 𝒮 n (DirectSum.of _ j a)) =
      DirectSum.toAddMonoid (fun k => DirectSum.of (fun i : ℕ => 𝒮 i) (n * k))
        (DirectSum.of _ j a)
    rw [DirectSum.toAddMonoid_of, inclusion_of, DirectSum.decompose_coe]
  | add x y hx hy =>
    rw [map_add, DirectSum.decompose_add, map_add, hx, hy]

theorem reindex_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (reindex 𝒮 n) := by
  intro x y hxy
  apply DirectSum.ext
  intro j
  have hdegree : Function.Injective (n * ·) := fun _ _ h => Nat.mul_left_cancel hn h
  have hleft (z : VeroneseRing 𝒮 n) :
      DFinsupp.comapDomain (n * ·) hdegree (reindex 𝒮 n z) = z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of k a =>
      simp only [reindex, DirectSum.toAddMonoid_of]
      exact DFinsupp.comapDomain_single (β := fun i : ℕ => ↥(𝒮 i))
        (n * ·) hdegree k a
    | add a b ha hb =>
      rw [map_add, DFinsupp.comapDomain_add, ha, hb]
  exact congrArg (fun z => z j) ((hleft x).symm.trans (congrArg _ hxy |>.trans (hleft y)))

/-- The selected-components ring embeds in the original graded ring, without a
regularity or domain assumption. -/
theorem inclusion_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (inclusion 𝒮 n) := by
  intro x y hxy
  apply reindex_injective 𝒮 n hn
  rw [← decompose_inclusion, ← decompose_inclusion, hxy]

/-- The concrete subring of finite sums of old components of degree divisible by `n`. -/
def subring (n : ℕ) : Subring S := (inclusion 𝒮 n).range

theorem mem_subring_iff (n : ℕ) (s : S) :
    s ∈ subring 𝒮 n ↔ ∃ x : VeroneseRing 𝒮 n, inclusion 𝒮 n x = s := by
  rfl

/-- The entire degree-zero component maps to the original degree-zero ring. -/
def zeroRingHom (n : ℕ) : component 𝒮 n 0 →+* 𝒮 0 where
  toFun a := ⟨inclusion 𝒮 n a, by
    simpa only [mul_zero] using inclusion_mem 𝒮 a.property⟩
  map_one' := Subtype.ext (map_one (inclusion 𝒮 n))
  map_mul' a b := Subtype.ext (map_mul (inclusion 𝒮 n) (a : VeroneseRing 𝒮 n) b)
  map_zero' := Subtype.ext (map_zero (inclusion 𝒮 n))
  map_add' a b := Subtype.ext (map_add (inclusion 𝒮 n) (a : VeroneseRing 𝒮 n) b)

/-- Identifies degree zero with the *whole* old degree-zero ring. -/
def zeroRingEquiv (n : ℕ) (hn : 0 < n) : component 𝒮 n 0 ≃+* 𝒮 0 :=
  RingEquiv.ofBijective (zeroRingHom 𝒮 n) ⟨by
    intro x y hxy
    apply Subtype.ext
    exact inclusion_injective 𝒮 n hn (congrArg Subtype.val hxy), by
      intro a
      obtain ⟨x, hx, heq⟩ := exists_component 𝒮 n 0 a
      exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩

@[simp] theorem zeroRingEquiv_apply (n : ℕ) (hn : 0 < n)
    (a : component 𝒮 n 0) :
    ((zeroRingEquiv 𝒮 n hn a : 𝒮 0) : S) = inclusion 𝒮 n a := rfl

end GradedRing.Veronese
