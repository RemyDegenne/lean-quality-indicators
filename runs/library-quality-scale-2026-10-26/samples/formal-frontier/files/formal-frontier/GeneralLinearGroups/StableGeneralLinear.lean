/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryStabilization
public import GeneralLinearGroups.Reindex
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Stable general linear groups

The initial-segment inclusions of finite general linear groups form a directed
system over the natural numbers. Its direct limit admits finite-stage representatives,
an eventual equality criterion, and a universal group homomorphism out of the limit.
All constructions work for semirings, including the zero semiring.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

/-- The specified identification of a first block and its complement with an
initial segment of `Fin m`. -/
def finBlockEquiv {n m : ℕ} (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp]
theorem finBlockEquiv_inl {n m : ℕ} (h : n ≤ m) (i : Fin n) :
    finBlockEquiv h (Sum.inl i) = Fin.castLE h i := by
  exact Fin.ext rfl

@[simp]
theorem finBlockEquiv_inr {n m : ℕ} (h : n ≤ m) (i : Fin (m - n)) :
    finBlockEquiv h (Sum.inr i) = Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i) := by
  rfl

/-- Embed an invertible matrix as the first diagonal block of a larger matrix,
with an identity complementary block. -/
def finStabilize (R : Type u) [Semiring R] {n m : ℕ} (h : n ≤ m) :
    GL (Fin n) R →* GL (Fin m) R :=
  (reindexEquiv R (finBlockEquiv h)).toMonoidHom.comp (stabilize (Y := Fin (m - n)))

@[simp]
theorem finStabilize_apply_inl_inl (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) (i j : Fin n) :
    finStabilize R h g (finBlockEquiv h (Sum.inl i))
        (finBlockEquiv h (Sum.inl j)) = g i j := by
  change reindexEquiv R (finBlockEquiv h) (stabilize (Y := Fin (m - n)) g)
    (finBlockEquiv h (Sum.inl i)) (finBlockEquiv h (Sum.inl j)) = g i j
  simp only [reindexEquiv_apply, Equiv.symm_apply_apply, stabilize_apply_inl_inl]

@[simp]
theorem finStabilize_apply_inl_inr (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R)
    (i : Fin n) (j : Fin (m - n)) :
    finStabilize R h g (finBlockEquiv h (Sum.inl i))
        (finBlockEquiv h (Sum.inr j)) = 0 := by
  change reindexEquiv R (finBlockEquiv h) (stabilize (Y := Fin (m - n)) g)
    (finBlockEquiv h (Sum.inl i)) (finBlockEquiv h (Sum.inr j)) = 0
  simp only [reindexEquiv_apply, Equiv.symm_apply_apply, stabilize_apply_inl_inr]

@[simp]
theorem finStabilize_apply_inr_inl (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R)
    (i : Fin (m - n)) (j : Fin n) :
    finStabilize R h g (finBlockEquiv h (Sum.inr i))
        (finBlockEquiv h (Sum.inl j)) = 0 := by
  change reindexEquiv R (finBlockEquiv h) (stabilize (Y := Fin (m - n)) g)
    (finBlockEquiv h (Sum.inr i)) (finBlockEquiv h (Sum.inl j)) = 0
  simp only [reindexEquiv_apply, Equiv.symm_apply_apply, stabilize_apply_inr_inl]

@[simp]
theorem finStabilize_apply_inr_inr (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R)
    (i j : Fin (m - n)) :
    finStabilize R h g (finBlockEquiv h (Sum.inr i))
        (finBlockEquiv h (Sum.inr j)) = (1 : Matrix (Fin (m - n)) (Fin (m - n)) R) i j := by
  change reindexEquiv R (finBlockEquiv h) (stabilize (Y := Fin (m - n)) g)
    (finBlockEquiv h (Sum.inr i)) (finBlockEquiv h (Sum.inr j)) =
      (1 : Matrix (Fin (m - n)) (Fin (m - n)) R) i j
  simp only [reindexEquiv_apply, Equiv.symm_apply_apply, stabilize_apply_inr_inr]

@[simp]
theorem finStabilize_apply_castLE (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) (i j : Fin n) :
    finStabilize R h g (Fin.castLE h i) (Fin.castLE h j) = g i j := by
  simpa only [finBlockEquiv_inl] using finStabilize_apply_inl_inl R h g i j

/-- Entries of an initial-segment stabilization are the original matrix in the
first block, zero in the off-diagonal blocks, and the identity elsewhere. -/
theorem finStabilize_apply (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) (i j : Fin m) :
    finStabilize R h g i j =
      if hi : i.val < n then
        if hj : j.val < n then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if j.val < n then 0 else if i.val = j.val then 1 else 0 := by
  obtain ⟨row, rfl⟩ := (finBlockEquiv h).surjective i
  obtain ⟨col, rfl⟩ := (finBlockEquiv h).surjective j
  rcases row with row | row <;> rcases col with col | col
  · simp only [finBlockEquiv_inl, Fin.val_castLE, dite_eq_left row.isLt,
      dite_eq_left col.isLt, finStabilize_apply_castLE]
  · have hcol : n ≤ (finBlockEquiv h (Sum.inr col)).val := by
      rw [finBlockEquiv_inr]
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    simp only [finBlockEquiv_inl, Fin.val_castLE, dite_eq_left row.isLt,
      dite_eq_right (not_lt.mpr hcol)]
    exact finStabilize_apply_inl_inr R h g row col
  · have hrow : n ≤ (finBlockEquiv h (Sum.inr row)).val := by
      rw [finBlockEquiv_inr]
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    simp only [finBlockEquiv_inl, Fin.val_castLE, ite_eq_left col.isLt,
      dite_eq_right (not_lt.mpr hrow)]
    exact finStabilize_apply_inr_inl R h g row col
  · have hrow : n ≤ (finBlockEquiv h (Sum.inr row)).val := by
      rw [finBlockEquiv_inr]
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    have hcol : n ≤ (finBlockEquiv h (Sum.inr col)).val := by
      rw [finBlockEquiv_inr]
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    simp only [dite_eq_right (not_lt.mpr hrow), ite_eq_right (not_lt.mpr hcol),
      finStabilize_apply_inr_inr, Matrix.one_apply]
    have heq : row = col ↔ (finBlockEquiv h (Sum.inr row)).val =
        (finBlockEquiv h (Sum.inr col)).val :=
      ⟨fun eq => by rw [eq],
        fun eq => Sum.inr_injective ((finBlockEquiv h).injective (Fin.ext eq))⟩
    simp only [heq]

@[simp]
theorem finStabilize_id (R : Type u) [Semiring R] (n : ℕ) :
    finStabilize R (le_refl n) = MonoidHom.id (GL (Fin n) R) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  simpa using finStabilize_apply_castLE R (le_refl n) g i j

@[simp]
theorem finStabilize_comp (R : Type u) [Semiring R]
    {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    finStabilize R (h.trans h') = (finStabilize R h').comp (finStabilize R h) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  rw [MonoidHom.comp_apply, finStabilize_apply R (h.trans h') g i j,
    finStabilize_apply R h' (finStabilize R h g) i j]
  split_ifs <;> try omega
  all_goals
    simp only [finStabilize_apply] <;>
      (try (split_ifs; try omega)) <;>
      rfl

/-- The upper-left block recovers the original invertible matrix. -/
theorem finStabilize_injective (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) : Function.Injective (finStabilize R h) := by
  intro g g' hg
  apply stabilize_injective (Y := Fin (m - n))
  exact (reindexEquiv R (finBlockEquiv h)).injective hg

@[simp]
theorem finStabilize_mapRingHom {R : Type u} {S : Type v}
    [Semiring R] [Semiring S] (f : R →+* S)
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) :
    finStabilize S h (mapRingHom f g) = mapRingHom f (finStabilize R h g) := by
  simp [finStabilize, mapRingHom_stabilize]

/-- The maps of the natural-number directed system of general linear groups. -/
def finStabilizeSystem (R : Type u) [Semiring R] :
    ∀ n m : ℕ, n ≤ m → GL (Fin n) R →* GL (Fin m) R :=
  fun _ _ h => finStabilize R h

instance (R : Type u) [Semiring R] :
    DirectedSystem (fun n : ℕ => GL (Fin n) R)
      (fun ⦃n m⦄ (h : n ≤ m) =>
        (finStabilizeSystem R n m h : GL (Fin n) R → GL (Fin m) R)) where
  map_self := by
    intro n g
    exact congrArg (fun phi : GL (Fin n) R →* GL (Fin n) R => phi g)
      (finStabilize_id R n)
  map_map := by
    intro k j i hij hjk g
    exact (congrArg (fun phi : GL (Fin i) R →* GL (Fin k) R => phi g)
      (finStabilize_comp R hij hjk)).symm

/-- The noncommutative direct limit of finite general linear groups under
initial-segment stabilization. -/
abbrev StableGL (R : Type u) [Semiring R] : Type u :=
  DirectLimit (fun n : ℕ => GL (Fin n) R) (finStabilizeSystem R)

namespace StableGL

/-- The canonical group homomorphism from a finite rank into stable GL. -/
def stage (R : Type u) [Semiring R] (n : ℕ) : GL (Fin n) R →* StableGL R where
  toFun g := (⟦⟨n, g⟩⟧ : StableGL R)
  map_one' := by
    exact (DirectLimit.one_def (f := finStabilizeSystem R) n).symm
  map_mul' g h := by
    exact (DirectLimit.mul_def (f := finStabilizeSystem R) n g h).symm

@[simp]
theorem stage_finStabilize (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) :
    stage R m (finStabilize R h g) = stage R n g := by
  change (⟦⟨m, (finStabilizeSystem R n m h) g⟩⟧ : StableGL R) = ⟦⟨n, g⟩⟧
  exact DirectLimit.mk_apply (f := finStabilizeSystem R) n m g h

/-- Each finite general linear group embeds into the stable group. -/
theorem stage_injective (R : Type u) [Semiring R] (n : ℕ) :
    Function.Injective (stage R n) :=
  DirectLimit.mk_injective (f := finStabilizeSystem R)
    (fun _ _ h => finStabilize_injective R h) n

/-- Every stable element is represented by an invertible matrix in some finite rank. -/
theorem exists_stage (R : Type u) [Semiring R] (g : StableGL R) :
    ∃ n : ℕ, ∃ x : GL (Fin n) R, stage R n x = g := by
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (finStabilizeSystem R) g
  exact ⟨n, x, rfl⟩

/-- Finite representatives coincide exactly when they agree at a common later rank. -/
theorem stage_eq_stage_iff (R : Type u) [Semiring R]
    {n m : ℕ} (x : GL (Fin n) R) (y : GL (Fin m) R) :
    stage R n x = stage R m y ↔
      ∃ k : ℕ, ∃ hn : n ≤ k, ∃ hm : m ≤ k,
        finStabilize R hn x = finStabilize R hm y := by
  exact Quotient.eq

/-- Lift a compatible family of group homomorphisms from finite ranks. -/
def lift (R : Type u) [Semiring R] {G : Type v} [Group G]
    (maps : ∀ n, GL (Fin n) R →* G)
    (compatible : ∀ n m (h : n ≤ m) (g : GL (Fin n) R),
      maps m (finStabilize R h g) = maps n g) : StableGL R →* G where
  toFun := DirectLimit.lift (finStabilizeSystem R) (fun n g => maps n g)
    (fun n m h g => (compatible n m h g).symm)
  map_one' := by
    exact DirectLimit.lift_one (f := finStabilizeSystem R) (fun n => maps n)
      (fun n m h g => (compatible n m h g).symm)
  map_mul' g h := by
    exact DirectLimit.lift_mul (f := finStabilizeSystem R) (fun n => maps n)
      (fun n m h x => (compatible n m h x).symm) g h

@[simp]
theorem lift_stage (R : Type u) [Semiring R] {G : Type v} [Group G]
    (maps : ∀ n, GL (Fin n) R →* G)
    (compatible : ∀ n m (h : n ≤ m) (g : GL (Fin n) R),
      maps m (finStabilize R h g) = maps n g)
    (n : ℕ) (g : GL (Fin n) R) :
    lift R maps compatible (stage R n g) = maps n g := rfl

@[ext]
theorem hom_ext (R : Type u) [Semiring R] {G : Type v} [Group G]
    {f g : StableGL R →* G}
    (h : ∀ n, f.comp (stage R n) = g.comp (stage R n)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := exists_stage R x
  exact congrArg (fun phi : GL (Fin n) R →* G => phi y) (h n)

/-- Map a stable invertible matrix entrywise along a semiring homomorphism. -/
noncomputable def map {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) : StableGL R →* StableGL S :=
  lift R (G := StableGL S) (fun n => (stage S n).comp (mapRingHom f))
    (by
      intro n m h g
      change stage S m (mapRingHom f (finStabilize R h g)) =
        stage S n (mapRingHom f g)
      rw [← finStabilize_mapRingHom f h g]
      exact stage_finStabilize S h (mapRingHom f g))

@[simp]
theorem map_stage {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (n : ℕ) (g : GL (Fin n) R) :
    map f (stage R n g) = stage S n (mapRingHom f g) := by
  exact lift_stage R _ _ n g

@[simp]
theorem map_id (R : Type u) [Semiring R] :
    map (RingHom.id R) = MonoidHom.id (StableGL R) := by
  apply hom_ext R
  intro n
  ext g
  simp

@[simp]
theorem map_comp {R : Type u} {S : Type v} {T : Type w}
    [Semiring R] [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext R
  intro n
  ext h
  simp

end StableGL
end Matrix.GeneralLinearGroup
