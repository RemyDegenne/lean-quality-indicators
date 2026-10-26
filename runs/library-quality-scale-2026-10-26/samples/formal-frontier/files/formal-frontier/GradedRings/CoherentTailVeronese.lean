/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Veronese
public import Mathlib.RingTheory.GradedAlgebra.RingHom

@[expose] public section

/-!
# Coherent tails of graded rings

Compatible equivalences of the degree-zero component and all sufficiently high
components induce an equivalence of the complete selected-component rings.
-/

noncomputable section

namespace GradedRing.Veronese.CoherentTail

open DirectSum

universe u v w z

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  {σ : Type v} {τ : Type z} [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Coherent identifications of degree zero and all degrees past a positive cutoff.
The products are the products of the original graded rings. -/
structure TailEquiv (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (N : ℕ)
    [GradedRing 𝒜] [GradedRing ℬ] where
  positive : 0 < N
  zero : 𝒜 0 ≃+* ℬ 0
  high : ∀ d, N ≤ d → 𝒜 d ≃+ ℬ d
  coeff : ∀ d (hd : N ≤ d) (a : 𝒜 0) (x : 𝒜 d),
    ((high d hd ⟨(a : R) * x, by
      simpa only [zero_add] using
        (SetLike.GradedMul.mul_mem a.property x.property :
          (a : R) * x ∈ 𝒜 (0 + d))⟩ : ℬ d) : S) =
      (zero a : S) * (high d hd x : S)
  product : ∀ d k (hd : N ≤ d) (hk : N ≤ k) (x : 𝒜 d) (y : 𝒜 k),
    ((high (d + k) (hd.trans (Nat.le_add_right d k))
      ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.property y.property⟩ : ℬ (d + k)) : S) =
      (high d hd x : S) * (high k hk y : S)

namespace TailEquiv

variable {N : ℕ}
variable (E : TailEquiv 𝒜 ℬ N) (n : ℕ) (hNn : N ≤ n)

/-- Identification of each component retained by the `n`th Veronese. -/
def pieceEquiv : (j : ℕ) → 𝒜 (n * j) ≃+ ℬ (n * j)
  | 0 => E.zero.toAddEquiv
  | j + 1 => E.high _ (by rw [mul_add, mul_one]; omega)

def pieceHom (j : ℕ) : 𝒜 (n * j) →+ VeroneseRing ℬ n :=
  (DirectSum.of (fun k : ℕ => ℬ (n * k)) j).comp (E.pieceEquiv n hNn j).toAddMonoidHom

theorem piece_cast (i j : ℕ) (h : i = j) (x : 𝒜 (n * i)) :
    (E.pieceEquiv n hNn i x : S) =
      (E.pieceEquiv n hNn j ⟨(x : R), by simpa only [← h] using x.property⟩ : S) := by
  subst j
  rfl

theorem high_cast (d k : ℕ) (hd : N ≤ d) (hk : N ≤ k) (h : d = k)
    (x : 𝒜 d) :
    (E.high d hd x : S) =
      (E.high k hk ⟨(x : R), by simpa only [← h] using x.property⟩ : S) := by
  subst k
  rfl

theorem piece_mul (i j : ℕ) (x : 𝒜 (n * i)) (y : 𝒜 (n * j)) :
    E.pieceEquiv n hNn (i + j)
      (GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k)) x y) =
      GradedMonoid.GMul.mul (A := fun k : ℕ => ℬ (n * k))
        (E.pieceEquiv n hNn i x) (E.pieceEquiv n hNn j y) := by
  cases i with
  | zero =>
    cases j with
    | zero =>
      apply Subtype.ext
      let xzero : 𝒜 0 := x
      let yzero : 𝒜 0 := y
      change ((E.zero (xzero * yzero) : ℬ 0) : S) =
        (E.zero x : S) * (E.zero y : S)
      exact congrArg Subtype.val (E.zero.map_mul xzero yzero)
    | succ j =>
      apply Subtype.ext
      have hd : N ≤ n * (j + 1) := by rw [mul_add, mul_one]; omega
      have hx : (x : R) ∈ 𝒜 0 := by simpa only [mul_zero] using x.property
      have hxy : (x : R) * y ∈ 𝒜 (n * (j + 1)) := by
        simpa only [zero_add] using SetLike.GradedMul.mul_mem hx y.property
      convert E.coeff (n * (j + 1)) hd x y using 1
      · convert E.piece_cast n hNn (0 + (j + 1)) (j + 1)
          (Nat.zero_add _) (GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k)) x y)
          using 1; rfl
      · change (E.zero x : S) * (E.high _ _ y : S) = _
        rfl
  | succ i =>
    cases j with
    | zero =>
      apply Subtype.ext
      have hi : N ≤ n * (i + 1) := by rw [mul_add, mul_one]; omega
      convert E.coeff (n * (i + 1)) hi y x using 1
      · convert E.piece_cast n hNn (i + 1 + 0) (i + 1) (Nat.add_zero _)
          (GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k)) x y)
          using 1
        congr 2
        apply Subtype.ext
        exact mul_comm (y : R) (x : R)
      · change (E.high _ _ x : S) * (E.zero y : S) =
          (E.zero y : S) * (E.high _ hi x : S)
        exact mul_comm _ _
    | succ j =>
      apply Subtype.ext
      have hi : N ≤ n * (i + 1) := by rw [mul_add, mul_one]; omega
      have hj : N ≤ n * (j + 1) := by rw [mul_add, mul_one]; omega
      have hdegree : n * ((i + 1) + (j + 1)) = n * (i + 1) + n * (j + 1) :=
        mul_add n _ _
      have hsum : N ≤ n * ((i + 1) + (j + 1)) := by
        rw [hdegree]
        omega
      convert E.product (n * (i + 1)) (n * (j + 1)) hi hj x y using 1
      · convert E.high_cast (n * ((i + 1) + (j + 1)))
          (n * (i + 1) + n * (j + 1)) hsum (by omega) hdegree
          (GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k)) x y)
          using 1; rfl
      · rfl

theorem piece_one :
    pieceHom E n hNn 0
      (GradedMonoid.GOne.one (A := fun k : ℕ => 𝒜 (n * k))) =
      (1 : VeroneseRing ℬ n) := by
  change DirectSum.of (fun k : ℕ => ℬ (n * k)) 0
    (E.pieceEquiv n hNn 0
      (GradedMonoid.GOne.one (A := fun k : ℕ => 𝒜 (n * k)))) = 1
  rw [DirectSum.one_def]
  congr 1
  apply Subtype.ext
  change ((E.zero (1 : 𝒜 0) : ℬ 0) : S) = 1
  exact congrArg Subtype.val (E.zero.map_one)

/-- The native ring map of the complete selected-component sums. -/
def selectedRingHom : VeroneseRing 𝒜 n →+* VeroneseRing ℬ n :=
  DirectSum.toSemiring (pieceHom E n hNn) (piece_one E n hNn)
    (by
      intro i j x y
      change DirectSum.of (fun k : ℕ => ℬ (n * k)) (i + j)
        (E.pieceEquiv n hNn (i + j)
          (GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k)) x y)) =
        DirectSum.of (fun k : ℕ => ℬ (n * k)) i (E.pieceEquiv n hNn i x) *
          DirectSum.of (fun k : ℕ => ℬ (n * k)) j (E.pieceEquiv n hNn j y)
      rw [DirectSum.of_mul_of, piece_mul E n hNn i j x y])

@[simp] theorem selectedRingHom_of (j : ℕ) (x : 𝒜 (n * j)) :
    E.selectedRingHom n hNn (DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j x) =
      DirectSum.of (fun k : ℕ => ℬ (n * k)) j (E.pieceEquiv n hNn j x) :=
  DirectSum.toSemiring_of _ _ _ _ _

theorem piece_mul_symm (i j : ℕ) (x : ℬ (n * i)) (y : ℬ (n * j)) :
    (E.pieceEquiv n hNn (i + j)).symm
      (GradedMonoid.GMul.mul (A := fun k : ℕ => ℬ (n * k)) x y) =
      GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k))
        ((E.pieceEquiv n hNn i).symm x) ((E.pieceEquiv n hNn j).symm y) := by
  apply (E.pieceEquiv n hNn (i + j)).injective
  simpa only [AddEquiv.apply_symm_apply] using
    (E.piece_mul n hNn i j ((E.pieceEquiv n hNn i).symm x)
      ((E.pieceEquiv n hNn j).symm y)).symm

def pieceHomSymm (j : ℕ) : ℬ (n * j) →+ VeroneseRing 𝒜 n :=
  (DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j).comp
    (E.pieceEquiv n hNn j).symm.toAddMonoidHom

theorem piece_one_symm :
    E.pieceHomSymm n hNn 0
      (GradedMonoid.GOne.one (A := fun k : ℕ => ℬ (n * k))) =
      (1 : VeroneseRing 𝒜 n) := by
  change DirectSum.of (fun k : ℕ => 𝒜 (n * k)) 0
    ((E.pieceEquiv n hNn 0).symm
      (GradedMonoid.GOne.one (A := fun k : ℕ => ℬ (n * k)))) = 1
  rw [DirectSum.one_def]
  congr 1
  apply Subtype.ext
  change ((E.zero.symm (1 : ℬ 0) : 𝒜 0) : R) = 1
  exact congrArg Subtype.val (E.zero.symm.map_one)

/-- The inverse ring map is constructed from the component inverses, not assumed. -/
def selectedRingHomSymm : VeroneseRing ℬ n →+* VeroneseRing 𝒜 n :=
  DirectSum.toSemiring (E.pieceHomSymm n hNn) (E.piece_one_symm n hNn)
    (by
      intro i j x y
      change DirectSum.of (fun k : ℕ => 𝒜 (n * k)) (i + j)
        ((E.pieceEquiv n hNn (i + j)).symm
          (GradedMonoid.GMul.mul (A := fun k : ℕ => ℬ (n * k)) x y)) =
        DirectSum.of (fun k : ℕ => 𝒜 (n * k)) i ((E.pieceEquiv n hNn i).symm x) *
          DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j ((E.pieceEquiv n hNn j).symm y)
      rw [DirectSum.of_mul_of, E.piece_mul_symm n hNn i j x y])

@[simp] theorem selectedRingHomSymm_of (j : ℕ) (x : ℬ (n * j)) :
    E.selectedRingHomSymm n hNn (DirectSum.of (fun k : ℕ => ℬ (n * k)) j x) =
      DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j ((E.pieceEquiv n hNn j).symm x) :=
  DirectSum.toSemiring_of _ _ _ _ _

theorem selectedRingHomSymm_comp :
    (E.selectedRingHomSymm n hNn).comp (E.selectedRingHom n hNn) =
      RingHom.id (VeroneseRing 𝒜 n) := by
  apply DirectSum.ringHom_ext
  intro j x
  simp

theorem selectedRingHom_comp_symm :
    (E.selectedRingHom n hNn).comp (E.selectedRingHomSymm n hNn) =
      RingHom.id (VeroneseRing ℬ n) := by
  apply DirectSum.ringHom_ext
  intro j x
  simp

/-- A ring equivalence of the whole published selected-component rings. -/
def selectedRingEquiv : VeroneseRing 𝒜 n ≃+* VeroneseRing ℬ n where
  __ := E.selectedRingHom n hNn
  invFun := E.selectedRingHomSymm n hNn
  left_inv x := by
    have h := E.selectedRingHomSymm_comp n hNn
    exact congrArg (fun f : VeroneseRing 𝒜 n →+* VeroneseRing 𝒜 n => f x) h
  right_inv x := by
    have h := E.selectedRingHom_comp_symm n hNn
    exact congrArg (fun f : VeroneseRing ℬ n →+* VeroneseRing ℬ n => f x) h

@[simp] theorem selectedRingEquiv_of (j : ℕ) (x : 𝒜 (n * j)) :
    E.selectedRingEquiv n hNn (DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j x) =
      DirectSum.of (fun k : ℕ => ℬ (n * k)) j (E.pieceEquiv n hNn j x) :=
  E.selectedRingHom_of n hNn j x

@[simp] theorem selectedRingEquiv_symm_of (j : ℕ) (x : ℬ (n * j)) :
    (E.selectedRingEquiv n hNn).symm (DirectSum.of (fun k : ℕ => ℬ (n * k)) j x) =
      DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j ((E.pieceEquiv n hNn j).symm x) :=
  E.selectedRingHomSymm_of n hNn j x

/-- The selected equivalence as a degree-preserving ring homomorphism. -/
def selectedGradedHom : component 𝒜 n →+*ᵍ component ℬ n where
  __ := E.selectedRingHom n hNn
  map_mem {i} {x} hx := by
    obtain ⟨a, rfl⟩ := (mem_component_iff 𝒜 n i x).mp hx
    rw [E.selectedRingHom_of]
    exact (mem_component_iff ℬ n i _).mpr ⟨E.pieceEquiv n hNn i a, rfl⟩

/-- The inverse degree-preserving ring homomorphism. -/
def selectedGradedHomSymm : component ℬ n →+*ᵍ component 𝒜 n where
  __ := E.selectedRingHomSymm n hNn
  map_mem {i} {x} hx := by
    obtain ⟨a, rfl⟩ := (mem_component_iff ℬ n i x).mp hx
    rw [E.selectedRingHomSymm_of]
    exact (mem_component_iff 𝒜 n i _).mpr ⟨(E.pieceEquiv n hNn i).symm a, rfl⟩

theorem selectedGradedHomSymm_comp :
    (E.selectedGradedHomSymm n hNn).comp (E.selectedGradedHom n hNn) =
      GradedRingHom.id (component 𝒜 n) := by
  apply GradedRingHom.ext
  intro x
  have h := E.selectedRingHomSymm_comp n hNn
  exact congrArg (fun f : VeroneseRing 𝒜 n →+* VeroneseRing 𝒜 n => f x) h

theorem selectedGradedHom_comp_symm :
    (E.selectedGradedHom n hNn).comp (E.selectedGradedHomSymm n hNn) =
      GradedRingHom.id (component ℬ n) := by
  apply GradedRingHom.ext
  intro x
  have h := E.selectedRingHom_comp_symm n hNn
  exact congrArg (fun f : VeroneseRing ℬ n →+* VeroneseRing ℬ n => f x) h

/-- Degree zero commutes with the original coefficient equivalence. -/
theorem selected_zero (hn : 0 < n) :
    (zeroRingEquiv ℬ n hn).toRingHom.comp
      (GradedRingHom.gradedZeroRingHom (E.selectedGradedHom n hNn)) =
      E.zero.toRingHom.comp (zeroRingEquiv 𝒜 n hn).toRingHom := by
  ext x
  obtain ⟨a, ha⟩ := (mem_component_iff 𝒜 n 0 (x : VeroneseRing 𝒜 n)).mp x.property
  have hx : (x : VeroneseRing 𝒜 n) =
      DirectSum.of (fun k : ℕ => 𝒜 (n * k)) 0 a := ha.symm
  have ha0 : zeroRingEquiv 𝒜 n hn x = a := by
    apply Subtype.ext
    change inclusion 𝒜 n x = (a : R)
    rw [hx, inclusion_of]
  change inclusion ℬ n (E.selectedRingHom n hNn x) =
    ((E.zero (zeroRingEquiv 𝒜 n hn x) : ℬ 0) : S)
  rw [hx, E.selectedRingHom_of, inclusion_of, ha0]
  rfl

end TailEquiv
end GradedRing.Veronese.CoherentTail
