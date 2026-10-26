/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.Diagonal
public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Native upper-triangular general linear groups

Invertible upper-triangular matrices form a subgroup of the matrix general
linear group over every commutative ring. Their diagonal is a split quotient
with kernel the existing upper-unitriangular subgroup *inside this subgroup*.
The U-first semidirect equivalence uses column normalization and commutes
with every ring homomorphism, including noninjective ones. This is a result
about groups of points, not a scheme base-change theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9, p. 42:
  the `T_n`, `U_n` and `D_n` subgroup functors on commutative algebras.
  The arbitrary-ring U-first semidirect equivalence is proved here, not
  attributed to this item.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` for
  matrix units and coefficient maps, and
  `Mathlib/LinearAlgebra/Matrix/Block.lean` for triangular matrix products,
  inverses and determinants.
* Mathlib, `Mathlib/Algebra/Group/Subgroup/Ker.lean` for homomorphism kernels,
  `Mathlib/GroupTheory/Subgroup/Centralizer.lean` for conjugation on a
  normalizer, `Mathlib/Algebra/Group/End.lean` for `MulAut.congr`, and
  `Mathlib/GroupTheory/SemidirectProduct.lean` for `lift` and Thomas
  Browning's `map` construction.
* `AlgebraicGroups/GroupTheory/Diagonal.lean` and
  `AlgebraicGroups/GroupScheme/Unitriangular.lean` supply the existing
  diagonal and unitriangular groups rather than replacement types.
-/

@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

/-- The subgroup of native invertible matrices corresponding to Milne's
upper-triangular `T_n` (item 2.9), over any commutative ring. Inversion uses
Mathlib's triangular-inverse theorem, not nonvanishing of the determinant. -/
def upperTriangularSubgroup : Subgroup (GeneralLinearGroup ι R) where
  carrier := {g | (g : Matrix ι ι R).IsUpperTriangular}
  one_mem' := by
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro left right upperLeft upperRight
    exact upperLeft.mul upperRight
  inv_mem' := by
    intro matrix upper
    have : Invertible (matrix : Matrix ι ι R) := Units.invertible matrix
    change ((matrix⁻¹ : GeneralLinearGroup ι R) : Matrix ι ι R).IsUpperTriangular
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular upper

/-- Invertible upper-triangular matrices, including empty indices and zero rings. -/
abbrev UpperTriangularGroup := upperTriangularSubgroup ι R

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]

/-- Inclusion into the native matrix general linear group. -/
def inclusion : UpperTriangularGroup ι R →* GeneralLinearGroup ι R :=
  (upperTriangularSubgroup ι R).subtype

@[ext] theorem ext {left right : UpperTriangularGroup ι R}
    (entries : ∀ row col, left.1 row col = right.1 row col) : left = right := by
  apply Subtype.ext
  exact GeneralLinearGroup.ext entries

/-- Apply a ring homomorphism to each matrix entry. -/
def map (ringHom : R →+* S) : UpperTriangularGroup ι R →* UpperTriangularGroup ι S where
  toFun matrix := ⟨GeneralLinearGroup.map ringHom matrix.1, matrix.2.map ringHom⟩
  map_one' := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map ringHom).map_one
  map_mul' left right := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map ringHom).map_mul left.1 right.1

@[simp] theorem map_apply (ringHom : R →+* S) (matrix : UpperTriangularGroup ι R)
    (row col : ι) : (map ringHom matrix).1 row col = ringHom (matrix.1 row col) :=
  GeneralLinearGroup.map_apply ringHom row col matrix.1

@[simp] theorem map_id (matrix : UpperTriangularGroup ι R) :
    map (RingHom.id R) matrix = matrix := by
  ext row col
  simp

theorem map_comp (ringHom : R →+* S) (nextHom : S →+* Q)
    (matrix : UpperTriangularGroup ι R) :
    map nextHom (map ringHom matrix) = map (nextHom.comp ringHom) matrix := by
  ext row col
  simp

theorem inclusion_map (ringHom : R →+* S) (matrix : UpperTriangularGroup ι R) :
    inclusion (map ringHom matrix) = GeneralLinearGroup.map ringHom (inclusion matrix) := rfl

/-- Every diagonal entry is a scalar unit, without assumptions on the ring. -/
theorem isUnit_entry (matrix : UpperTriangularGroup ι R) (row : ι) :
    IsUnit (matrix.1 row row) := by
  have determinant : IsUnit (∏ index, matrix.1 index index) := by
    rw [← Matrix.det_of_isUpperTriangular matrix.2]
    exact isUnits_det_units matrix.1
  exact (IsUnit.prod_univ_iff.mp determinant) row

/-- Project an upper-triangular matrix to its invertible diagonal. -/
def diagonal : UpperTriangularGroup ι R →* DiagonalGroup ι R where
  toFun matrix := (DiagonalGroup.unitsEquiv (R := R)).symm
    (fun row => (isUnit_entry matrix row).unit)
  map_one' := by
    apply DiagonalGroup.ext
    intro row
    change ((DiagonalGroup.unitsEquiv (R := R)).symm
      (fun index : ι => (isUnit_entry (1 : UpperTriangularGroup ι R) index).unit)).1 row row =
      (1 : DiagonalGroup ι R).1 row row
    simp [DiagonalGroup.unitsEquiv_symm_apply]
  map_mul' left right := by
    apply DiagonalGroup.ext
    intro row
    change ((DiagonalGroup.unitsEquiv (R := R)).symm
      (fun index : ι => (isUnit_entry (left * right) index).unit)).1 row row =
      ((DiagonalGroup.unitsEquiv (R := R)).symm
        (fun index : ι => (isUnit_entry left index).unit) *
        (DiagonalGroup.unitsEquiv (R := R)).symm
        (fun index : ι => (isUnit_entry right index).unit)).1 row row
    rw [← map_mul (DiagonalGroup.unitsEquiv (R := R)).symm]
    simp only [DiagonalGroup.unitsEquiv_symm_apply, IsUnit.unit_spec]
    exact UnitriangularCoordinateRing.upper_mul_diag left.2 right.2 row

@[simp] theorem diagonal_apply_diag (matrix : UpperTriangularGroup ι R) (row : ι) :
    (diagonal matrix).1 row row = matrix.1 row row := by
  simp [diagonal, DiagonalGroup.unitsEquiv_symm_apply]

theorem diagonal_apply (matrix : UpperTriangularGroup ι R) (row col : ι) :
    (diagonal matrix).1 row col = if row = col then matrix.1 row row else 0 := by
  split_ifs with equal
  · subst col
    exact diagonal_apply_diag matrix row
  · exact (diagonal matrix).2 row col equal

/-- Include a native diagonal group element as an upper-triangular element. -/
def diagonalSection : DiagonalGroup ι R →* UpperTriangularGroup ι R where
  toFun matrix := ⟨matrix.1, by
    change (matrix.1 : Matrix ι ι R).IsUpperTriangular
    intro row col below
    exact matrix.2 row col (ne_of_gt below)⟩
  map_one' := Subtype.ext (by rfl)
  map_mul' _ _ := Subtype.ext (by rfl)

@[simp] theorem diagonal_section (matrix : DiagonalGroup ι R) :
    diagonal (diagonalSection matrix) = matrix := by
  apply DiagonalGroup.ext
  intro row
  exact diagonal_apply_diag _ row

theorem diagonal_surjective : Function.Surjective (diagonal (ι := ι) (R := R)) :=
  fun matrix => ⟨diagonalSection matrix, diagonal_section matrix⟩

theorem diagonal_map (ringHom : R →+* S) (matrix : UpperTriangularGroup ι R) :
    diagonal (map ringHom matrix) = DiagonalGroup.map ringHom (diagonal matrix) := by
  apply DiagonalGroup.ext
  intro row
  simp

theorem diagonalSection_map (ringHom : R →+* S) (matrix : DiagonalGroup ι R) :
    map ringHom (diagonalSection matrix) = diagonalSection (DiagonalGroup.map ringHom matrix) :=
  rfl

end UpperTriangularGroup

namespace UnitriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Inclusion of the published unitriangular group into upper-triangular units. -/
def inUpperTriangular : UnitriangularGroup ι R →* UpperTriangularGroup ι R where
  toFun unit := ⟨unit.1, unit.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inUpperTriangular_injective :
    Function.Injective (inUpperTriangular (ι := ι) (R := R)) := by
  intro left right equal
  exact Subtype.ext (congrArg (fun matrix : UpperTriangularGroup ι R => matrix.1) equal)

theorem inUpperTriangular_map (ringHom : R →+* S) (unit : UnitriangularGroup ι R) :
    UpperTriangularGroup.map ringHom (inUpperTriangular unit) =
      inUpperTriangular (map ringHom unit) := rfl

end UnitriangularGroup

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The diagonal kernel is precisely the image of the existing unitriangular
group as a subgroup of `UpperTriangularGroup`, not a subgroup of all GL. -/
theorem range_unitriangular :
    (UnitriangularGroup.inUpperTriangular (ι := ι) (R := R)).range =
      (diagonal (ι := ι) (R := R)).ker := by
  apply Subgroup.ext
  intro matrix
  constructor
  · rintro ⟨unit, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply DiagonalGroup.ext
    intro row
    rw [diagonal_apply_diag]
    change (unit.1 : Matrix ι ι R) row row = (1 : GeneralLinearGroup ι R) row row
    simpa using unit.2.2 row
  · intro kernel
    refine ⟨⟨matrix.1, ⟨matrix.2, ?_⟩⟩, rfl⟩
    intro row
    have equality : diagonal matrix = 1 := MonoidHom.mem_ker.mp kernel
    have entry := congrArg (fun diag : DiagonalGroup ι R => diag.1 row row) equality
    simpa [diagonal_apply_diag] using entry

/-- The published unitriangular group is the actual projection kernel. -/
def kernelEquiv : UnitriangularGroup ι R ≃* (diagonal (ι := ι) (R := R)).ker where
  toFun unit := ⟨UnitriangularGroup.inUpperTriangular unit, by
    rw [← range_unitriangular]
    exact ⟨unit, rfl⟩⟩
  invFun kernel := ⟨kernel.1.1, ⟨kernel.1.2, by
    intro row
    have entry := congrArg (fun diag : DiagonalGroup ι R => diag.1 row row)
      (MonoidHom.mem_ker.mp kernel.2)
    simpa [diagonal_apply_diag] using entry⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem kernelEquiv_val (unit : UnitriangularGroup ι R) :
    (kernelEquiv unit).1 = UnitriangularGroup.inUpperTriangular unit := rfl

/-- Diagonal conjugation on the existing unitriangular group, transported
through Mathlib's normalizer action and `MulAut.congr`. The entrywise weight
is `dᵢ * uᵢⱼ * dⱼ⁻¹`; normality in all of GL is not claimed. -/
def diagonalAction : DiagonalGroup ι R →* MulAut (UnitriangularGroup ι R) :=
  (MulAut.congr (kernelEquiv (ι := ι) (R := R)).symm).toMonoidHom.comp
    (((diagonal (ι := ι) (R := R)).ker.normalizerMonoidHom).comp
      ((diagonalSection (ι := ι) (R := R)).codRestrict _
        (fun _ => by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top])))

/-- The action is conjugation inside the actual upper-triangular matrix group. -/
theorem inUpperTriangular_diagonalAction (diag : DiagonalGroup ι R)
    (unit : UnitriangularGroup ι R) :
    UnitriangularGroup.inUpperTriangular (diagonalAction diag unit) =
      diagonalSection diag * UnitriangularGroup.inUpperTriangular unit *
        (diagonalSection diag)⁻¹ := by
  rfl

@[simp] theorem diagonal_inUpperTriangular (unit : UnitriangularGroup ι R) :
    diagonal (UnitriangularGroup.inUpperTriangular unit) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [← range_unitriangular]
  exact ⟨unit, rfl⟩

/-- Recover the unitriangular factor by column normalization. -/
def unipotentPart (matrix : UpperTriangularGroup ι R) : UnitriangularGroup ι R :=
  (kernelEquiv (ι := ι) (R := R)).symm
    ⟨matrix * diagonalSection (diagonal matrix)⁻¹, by
      apply MonoidHom.mem_ker.mpr
      simp⟩

theorem inUpperTriangular_unipotentPart (matrix : UpperTriangularGroup ι R) :
    UnitriangularGroup.inUpperTriangular (unipotentPart matrix) =
      matrix * diagonalSection (diagonal matrix)⁻¹ := by
  rfl

@[simp] theorem unipotentPart_factor (matrix : UpperTriangularGroup ι R) :
    UnitriangularGroup.inUpperTriangular (unipotentPart matrix) *
      diagonalSection (diagonal matrix) = matrix := by
  rw [inUpperTriangular_unipotentPart]
  exact mul_inv_cancel_right matrix _

/-- The U-first product map, whose multiplication uses diagonal conjugation. -/
def semidirHom :
    (UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] DiagonalGroup ι R) →*
      UpperTriangularGroup ι R :=
  SemidirectProduct.lift UnitriangularGroup.inUpperTriangular diagonalSection (by
    intro diag
    apply MonoidHom.ext
    intro unit
    exact inUpperTriangular_diagonalAction diag unit)

@[simp] theorem semidirHom_apply
    (coords : UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      DiagonalGroup ι R) :
    semidirHom coords = UnitriangularGroup.inUpperTriangular coords.left *
      diagonalSection coords.right := rfl

@[simp] theorem diagonal_semidirHom
    (coords : UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      DiagonalGroup ι R) : diagonal (semidirHom coords) = coords.right := by
  rw [semidirHom_apply, map_mul, diagonal_inUpperTriangular, diagonal_section, one_mul]

/-- Every upper-triangular matrix factors uniquely as a unitriangular matrix
times its diagonal. Mathlib's `SemidirectProduct.lift` encodes the U-first
product with diagonal conjugation; the inverse is column normalization.
Milne, *Algebraic Groups* (2017), item 2.9 describes the subgroup functors,
not this arbitrary-ring splitting of their point groups. -/
def semidirEquiv :
    (UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] DiagonalGroup ι R) ≃*
      UpperTriangularGroup ι R :=
  MulEquiv.ofBijective semidirHom (by
    constructor
    · intro left right equal
      have diagEqual : left.right = right.right := by
        have mapped := congrArg diagonal equal
        simpa using mapped
      have unitEqual : left.left = right.left := by
        apply UnitriangularGroup.inUpperTriangular_injective
        have canceled := congrArg
          (fun matrix : UpperTriangularGroup ι R => matrix *
            (diagonalSection left.right)⁻¹) equal
        simpa [semidirHom_apply, diagEqual, mul_assoc] using canceled
      exact SemidirectProduct.ext unitEqual diagEqual
    · intro matrix
      refine ⟨⟨unipotentPart matrix, diagonal matrix⟩, ?_⟩
      exact unipotentPart_factor matrix)

@[simp] theorem semidirEquiv_apply
    (coords : UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      DiagonalGroup ι R) :
    semidirEquiv coords = UnitriangularGroup.inUpperTriangular coords.left *
      diagonalSection coords.right := rfl

@[simp] theorem semidirEquiv_symm_left (matrix : UpperTriangularGroup ι R) :
    (semidirEquiv.symm matrix).left = unipotentPart matrix := by
  apply UnitriangularGroup.inUpperTriangular_injective
  have factor := congrArg (fun value : UpperTriangularGroup ι R =>
      value * (diagonalSection (diagonal matrix))⁻¹)
    (semidirEquiv.apply_symm_apply matrix)
  have diagEq : (semidirEquiv.symm matrix).right = diagonal matrix := by
    have mapped := congrArg diagonal (semidirEquiv.apply_symm_apply matrix)
    simpa only [semidirEquiv_apply, map_mul, diagonal_inUpperTriangular,
      diagonal_section, one_mul] using mapped
  rw [semidirEquiv_apply, diagEq, mul_inv_cancel_right] at factor
  exact factor.trans (inUpperTriangular_unipotentPart matrix).symm

@[simp] theorem semidirEquiv_symm_right (matrix : UpperTriangularGroup ι R) :
    (semidirEquiv.symm matrix).right = diagonal matrix := by
  have mapped := congrArg diagonal (semidirEquiv.apply_symm_apply matrix)
  simpa only [semidirEquiv_apply, map_mul, diagonal_inUpperTriangular,
    diagonal_section, one_mul] using mapped

/-- Column normalization uses the unit in the *column* of the input matrix. -/
theorem unipotentPart_apply (matrix : UpperTriangularGroup ι R) (row col : ι) :
    (unipotentPart matrix).1 row col = matrix.1 row col *
      (((DiagonalGroup.unitsEquiv (diagonal matrix) col)⁻¹ : Rˣ) : R) := by
  have entry := congrArg (fun value : UpperTriangularGroup ι R => value.1 row col)
    (inUpperTriangular_unipotentPart matrix)
  change (unipotentPart matrix).1 row col = ((matrix.1 : Matrix ι ι R) *
    (((diagonalSection (diagonal matrix))⁻¹).1 : Matrix ι ι R)) row col at entry
  rw [← map_inv diagonalSection] at entry
  have diagMatrix (diag : DiagonalGroup ι R) :
      (diag.1 : Matrix ι ι R) = Matrix.diagonal (fun index => diag.1 index index) := by
    ext index other
    by_cases equal : index = other
    · subst other
      simp
    · simp [diag.2 index other equal, Matrix.diagonal_apply_ne _ equal]
  change (unipotentPart matrix).1 row col = ((matrix.1 : Matrix ι ι R) *
    (((diagonal matrix)⁻¹).1 : Matrix ι ι R)) row col at entry
  rw [diagMatrix ((diagonal matrix)⁻¹), Matrix.mul_diagonal] at entry
  rw [← DiagonalGroup.unitsEquiv_apply_val ((diagonal matrix)⁻¹) col,
    map_inv (DiagonalGroup.unitsEquiv (R := R)) (diagonal matrix)] at entry
  exact entry

/-- The conjugation action has the expected two-sided scalar weight. -/
theorem diagonalAction_apply (diag : DiagonalGroup ι R)
    (unit : UnitriangularGroup ι R) (row col : ι) :
    (diagonalAction diag unit).1 row col =
      (DiagonalGroup.unitsEquiv diag row : Rˣ) * unit.1 row col *
        (((DiagonalGroup.unitsEquiv diag col)⁻¹ : Rˣ) : R) := by
  have diagMatrix (value : DiagonalGroup ι R) :
      (value.1 : Matrix ι ι R) = Matrix.diagonal (fun index => value.1 index index) := by
    ext index other
    by_cases equal : index = other
    · subst other
      simp
    · simp [value.2 index other equal, Matrix.diagonal_apply_ne _ equal]
  have acted := congrArg (fun matrix : UpperTriangularGroup ι R => matrix.1 row col)
    (inUpperTriangular_diagonalAction diag unit)
  change (diagonalAction diag unit).1 row col =
    (((diag.1 : Matrix ι ι R) * (unit.1 : Matrix ι ι R) *
      ((diag⁻¹).1 : Matrix ι ι R)) row col) at acted
  rw [diagMatrix diag, diagMatrix (diag⁻¹), Matrix.mul_diagonal,
    Matrix.diagonal_mul] at acted
  rw [← DiagonalGroup.unitsEquiv_apply_val diag row,
    ← DiagonalGroup.unitsEquiv_apply_val (diag⁻¹) col,
    map_inv (DiagonalGroup.unitsEquiv (R := R)) diag] at acted
  exact acted

/-- Entrywise maps commute with column normalization, without assuming injectivity. -/
theorem unipotentPart_map (ringHom : R →+* S) (matrix : UpperTriangularGroup ι R) :
    UnitriangularGroup.map ringHom (unipotentPart matrix) =
      unipotentPart (map ringHom matrix) := by
  apply UnitriangularGroup.inUpperTriangular_injective
  calc
    UnitriangularGroup.inUpperTriangular (UnitriangularGroup.map ringHom
        (unipotentPart matrix)) =
        map ringHom (UnitriangularGroup.inUpperTriangular (unipotentPart matrix)) :=
      (UnitriangularGroup.inUpperTriangular_map ringHom _).symm
    _ = map ringHom matrix *
        (diagonalSection (diagonal (map ringHom matrix)))⁻¹ := by
      rw [inUpperTriangular_unipotentPart, map_mul]
      simp [map_inv, diagonalSection_map, diagonal_map]
    _ = UnitriangularGroup.inUpperTriangular (unipotentPart (map ringHom matrix)) :=
      (inUpperTriangular_unipotentPart _).symm

/-- Native diagonal conjugation commutes with every ring homomorphism. -/
theorem diagonalAction_map (ringHom : R →+* S) (diag : DiagonalGroup ι R)
    (unit : UnitriangularGroup ι R) :
    UnitriangularGroup.map ringHom (diagonalAction diag unit) =
      diagonalAction (DiagonalGroup.map ringHom diag) (UnitriangularGroup.map ringHom unit) := by
  apply UnitriangularGroup.inUpperTriangular_injective
  calc
    UnitriangularGroup.inUpperTriangular (UnitriangularGroup.map ringHom
        (diagonalAction diag unit)) =
        map ringHom (UnitriangularGroup.inUpperTriangular (diagonalAction diag unit)) :=
      (UnitriangularGroup.inUpperTriangular_map ringHom _).symm
    _ = diagonalSection (DiagonalGroup.map ringHom diag) *
        UnitriangularGroup.inUpperTriangular (UnitriangularGroup.map ringHom unit) *
          (diagonalSection (DiagonalGroup.map ringHom diag))⁻¹ := by
      rw [inUpperTriangular_diagonalAction, map_mul, map_mul, map_inv,
        diagonalSection_map, UnitriangularGroup.inUpperTriangular_map]
    _ = UnitriangularGroup.inUpperTriangular
        (diagonalAction (DiagonalGroup.map ringHom diag)
          (UnitriangularGroup.map ringHom unit)) :=
      (inUpperTriangular_diagonalAction _ _).symm

/-- The natural coefficient-change map of U-first semidirect products. -/
def semidirMap (ringHom : R →+* S) :
    (UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] DiagonalGroup ι R) →*
      (UnitriangularGroup ι S ⋊[diagonalAction (ι := ι) (R := S)] DiagonalGroup ι S) :=
  SemidirectProduct.map (UnitriangularGroup.map ringHom) (DiagonalGroup.map ringHom) (by
    intro diag
    apply MonoidHom.ext
    intro unit
    exact diagonalAction_map ringHom diag unit)

theorem semidirEquiv_map (ringHom : R →+* S)
    (coords : UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      DiagonalGroup ι R) :
    map ringHom (semidirEquiv coords) = semidirEquiv (semidirMap ringHom coords) := by
  simp [semidirEquiv_apply, semidirMap, map_mul, diagonalSection_map,
    UnitriangularGroup.inUpperTriangular_map]

theorem semidirEquiv_symm_map (ringHom : R →+* S)
    (matrix : UpperTriangularGroup ι R) :
    semidirMap ringHom (semidirEquiv.symm matrix) =
      semidirEquiv.symm (map ringHom matrix) := by
  apply (semidirEquiv (ι := ι) (R := S)).injective
  rw [semidirEquiv.apply_symm_apply, ← semidirEquiv_map,
    semidirEquiv.apply_symm_apply]

@[simp] theorem semidirEquiv_inl (unit : UnitriangularGroup ι R) :
    semidirEquiv (SemidirectProduct.inl unit) =
      UnitriangularGroup.inUpperTriangular unit := by
  simp [semidirEquiv_apply]

@[simp] theorem semidirEquiv_inr (diag : DiagonalGroup ι R) :
    semidirEquiv (SemidirectProduct.inr diag) = diagonalSection diag := by
  simp [semidirEquiv_apply]

theorem semidirEquiv_mul_formula (first second :
    UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] DiagonalGroup ι R) :
    UnitriangularGroup.inUpperTriangular first.left * diagonalSection first.right *
      (UnitriangularGroup.inUpperTriangular second.left * diagonalSection second.right) =
    UnitriangularGroup.inUpperTriangular
        (first.left * diagonalAction first.right second.left) *
      diagonalSection (first.right * second.right) := by
  simpa only [← semidirEquiv_apply, ← SemidirectProduct.mul_left,
    ← SemidirectProduct.mul_right] using (semidirEquiv.map_mul first second).symm

end UpperTriangularGroup

end Matrix
