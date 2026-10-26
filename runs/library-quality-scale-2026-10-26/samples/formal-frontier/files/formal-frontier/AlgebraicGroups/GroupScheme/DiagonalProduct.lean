/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineHomOver
public import AlgebraicGroups.GroupScheme.Diagonal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# The diagonal group scheme is a finite product of multiplicative groups

Milne identifies the diagonal subgroup over a field with a finite product of
`Gₘ`. Here actual Hopf-coordinate projections and the global-sections
adjunction establish the categorical product for **all** test schemes over
any commutative base, not merely affine test-algebra points. The empty-index
product is terminal.

The affine-target/global-sections equivalence and its composition law are
`affineSpecHomOverEquiv` and `affineSpecHomOverEquiv_comp`, provided by
`AlgebraicGroups.GroupScheme.AffineHomOver`. The names `diagonalAffineHomEquiv`
and `diagonalAffineHomEquiv_comp` remain as deprecated compatibility interfaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.9 (p. 42) for diagonal `D_n`,
  and §12.d (p. 234, after Definition 12.11) for `D_n` as a product of `Gₘ`.
* Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine`
  (`algΓAlgSpecAdjunction` and `hopfSpec`),
  `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits` (limits created by
  `Grp.forget`), `Mathlib.CategoryTheory.Limits.Shapes.Products` (fans and
  product projections), and `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal`
  (empty-product terminality).
* `AlgebraicGroups.GroupScheme.Multiplicative` for Laurent-coordinate units
  and `AlgebraicGroups.GroupScheme.Diagonal` for the diagonal Hopf quotient
  and its group-valued algebra points.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Pullback of the `j`-th Laurent coordinate along the diagonal projection. -/
def diagonalGroupProjectionCoordinateMap (j : n) :
    multiplicativeGroupCoordinateRing K →ₐ[K] DiagonalCoordinateRing.CoordinateRing K n :=
  (multiplicativeGroupMulEquivAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)
    (Matrix.DiagonalGroup.unitsEquiv (universal K n) j)).ofConv

@[simp] theorem diagonalGroupProjection_coordinate (j : n) :
    diagonalGroupProjectionCoordinateMap K n j (multiplicativeGroupCoordinate K) =
      quotient K n (matrix K n j j) := by
  rw [diagonalGroupProjectionCoordinateMap,
    multiplicativeGroupMulEquivAlgHom_coordinate,
    Matrix.DiagonalGroup.unitsEquiv_apply_val, DiagonalCoordinateRing.universal_apply]

private theorem diagonalGroupLaurent_ext {R : Type u} [CommRing R] [Algebra K R]
    {f g : multiplicativeGroupCoordinateRing K →ₐ[K] R}
    (h : f (multiplicativeGroupCoordinate K) = g (multiplicativeGroupCoordinate K)) :
    f = g := by
  let equiv := multiplicativeGroupMulEquivAlgHom K R
  let first := equiv.symm (WithConv.toConv f)
  let second := equiv.symm (WithConv.toConv g)
  have heq : first = second := by
    apply Units.ext
    rw [← multiplicativeGroupMulEquivAlgHom_coordinate K R first,
      ← multiplicativeGroupMulEquivAlgHom_coordinate K R second]
    simpa [first, second, equiv] using h
  have := congrArg (fun value : Rˣ ↦ (equiv value).ofConv) heq
  simpa [first, second, equiv] using this

private theorem diagonalGroupCoordinate_counit (j : n) :
    Coalgebra.counit (R := K) (quotient K n (matrix K n j j)) = 1 := by
  change Coalgebra.counit (R := K)
    (Ideal.Quotient.mk (ideal K n) (matrix K n j j)) = 1
  rw [Bialgebra.Quotient.counit_mk, native_counit_matrix]
  simp

private theorem diagonalGroupCoordinate_comul (j : n) :
    Coalgebra.comul (R := K) (quotient K n (matrix K n j j)) =
      quotient K n (matrix K n j j) ⊗ₜ[K] quotient K n (matrix K n j j) := by
  change Coalgebra.comul (R := K)
    (Ideal.Quotient.mk (ideal K n) (matrix K n j j)) = _
  rw [Bialgebra.Quotient.comul_mk]
  change (Algebra.TensorProduct.map (quotient K n) (quotient K n))
    (Coalgebra.comul (R := K) (matrix K n j j)) = _
  rw [native_comul_matrix, map_sum]
  apply Finset.sum_eq_single j
  · intro index _ hindex
    rw [Algebra.TensorProduct.map_tmul,
      quotient_offDiagonal K n j index hindex.symm, TensorProduct.zero_tmul]
  · simp [Algebra.TensorProduct.map_tmul]

/-- Each diagonal entry is group-like, giving a Hopf-algebra projection to
one `Gₘ` factor of Milne's diagonal product (*Algebraic Groups*, §12.d). -/
def diagonalGroupProjectionBialgHom (j : n) :
    multiplicativeGroupCoordinateRing K →ₐc[K] DiagonalCoordinateRing.CoordinateRing K n :=
  BialgHom.ofAlgHom (diagonalGroupProjectionCoordinateMap K n j)
    (by
      apply diagonalGroupLaurent_ext K
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
        diagonalGroupProjection_coordinate, diagonalGroupCoordinate_counit,
        multiplicativeGroupCoordinate_counit])
    (by
      let : CommRing (DiagonalCoordinateRing.CoordinateRing K n ⊗[K]
        DiagonalCoordinateRing.CoordinateRing K n) := inferInstance
      apply diagonalGroupLaurent_ext K
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        multiplicativeGroupCoordinate_comul, Algebra.TensorProduct.map_tmul,
        diagonalGroupProjection_coordinate, diagonalGroupCoordinate_comul])

/-- The `j`-th projection as a morphism of group objects over `Spec K`. -/
def diagonalGroupProjection (j : n) :
    diagonalGroupScheme K n ⟶ multiplicativeGroupScheme K :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (diagonalGroupProjectionBialgHom K n j)))

@[simp] theorem diagonalGroupProjection_left (j : n) :
    (diagonalGroupProjection K n j).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (diagonalGroupProjectionCoordinateMap K n j).toRingHom) := rfl

/-- A projection of a diagonal point is its corresponding invertible entry. -/
theorem diagonalGroupProjection_point (R : Type u) [CommRing R] [Algebra K R]
    (diagonal : Matrix.DiagonalGroup n R) (j : n) :
    diagonalGroupMulEquivPoints K n R diagonal ≫
      (diagonalGroupProjection K n j).hom.hom =
        multiplicativeGroupMulEquivPoints K R
          (Matrix.DiagonalGroup.unitsEquiv diagonal j) := by
  have hcoordinate : (diagonalGroupMulEquivAlgHom K n R diagonal).ofConv.comp
      (diagonalGroupProjectionCoordinateMap K n j) =
      (multiplicativeGroupMulEquivAlgHom K R
        (Matrix.DiagonalGroup.unitsEquiv diagonal j)).ofConv := by
    apply diagonalGroupLaurent_ext K
    rw [AlgHom.comp_apply, diagonalGroupProjection_coordinate,
      diagonalGroupMulEquivAlgHom_entry,
      multiplicativeGroupMulEquivAlgHom_coordinate]
    exact (Matrix.DiagonalGroup.unitsEquiv_apply_val diagonal j).symm
  apply Over.OverMorphism.ext
  rw [Over.comp_left, diagonalGroupMulEquivPoints_apply_left,
    diagonalGroupProjection_left, multiplicativeGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom
      (diagonalGroupMulEquivAlgHom K n R diagonal).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (diagonalGroupProjectionCoordinateMap K n j).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (multiplicativeGroupMulEquivAlgHom K R
        (Matrix.DiagonalGroup.unitsEquiv diagonal j)).ofConv.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun hom : multiplicativeGroupCoordinateRing K →ₐ[K] R ↦
    Spec.map (CommRingCat.ofHom hom.toRingHom)) hcoordinate

/-- Maps to an affine target are algebra maps into global sections.
Use `affineSpecHomOverEquiv`. -/
@[deprecated (since := "2026-10-16")]
alias diagonalAffineHomEquiv := affineSpecHomOverEquiv

/-- Postcomposition with an affine-target map acts by precomposition on
algebra maps into global sections. Use `affineSpecHomOverEquiv_comp`. -/
@[deprecated affineSpecHomOverEquiv_comp (since := "2026-10-16")]
theorem diagonalAffineHomEquiv_comp (X : Over (Spec (.of K)))
    (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (map : B →ₐ[K] A)
    (hom : X ⟶ (algSpec (.of K)).obj (.op (CommAlgCat.of K A))) :
    affineSpecHomOverEquiv K X B
      (hom ≫ (algSpec (.of K)).map (CommAlgCat.ofHom map).op) =
      (affineSpecHomOverEquiv K X A hom).comp map :=
  affineSpecHomOverEquiv_comp K X A B map hom

/-- Maps from any `K`-scheme to the diagonal group are tuples of global units,
using Mathlib's `algΓAlgSpecAdjunction`, also when the source is nonaffine. -/
def diagonalGroupHomUnits (X : Over (Spec (.of K))) :
    (X ⟶ (diagonalGroupScheme K n).X) ≃
      (n → ((algΓ (.of K)).obj X).unopˣ) :=
  (((affineSpecHomOverEquiv K X (DiagonalCoordinateRing.CoordinateRing K n)).trans
    (WithConv.equiv (DiagonalCoordinateRing.CoordinateRing K n →ₐ[K]
      ((algΓ (.of K)).obj X).unop)).symm).trans
    (diagonalGroupMulEquivAlgHom K n _).symm.toEquiv).trans
      Matrix.DiagonalGroup.unitsEquiv.toEquiv

/-- Maps from any `K`-scheme to `Gₘ` are its invertible global sections. -/
def multiplicativeGroupHomUnits (X : Over (Spec (.of K))) :
    (X ⟶ (multiplicativeGroupScheme K).X) ≃
      ((algΓ (.of K)).obj X).unopˣ :=
  ((affineSpecHomOverEquiv K X (multiplicativeGroupCoordinateRing K)).trans
    (WithConv.equiv (multiplicativeGroupCoordinateRing K →ₐ[K]
      ((algΓ (.of K)).obj X).unop)).symm).trans
    (multiplicativeGroupMulEquivAlgHom K _).symm.toEquiv

-- Keep the inverse map's declared target in the form carrying Mathlib's
-- canonical bialgebra-induced monoid structure.
private def diagonalAffineHomOfConv
    (X : Over (Spec (.of K))) (A : Type u) [CommRing A] [Algebra K A]
    (φ : WithConv (A →ₐ[K] ((algΓ (.of K)).obj X).unop)) :
    X ⟶ (Spec (.of A)).asOver (Spec (.of K)) :=
  (affineSpecHomOverEquiv K X A).symm φ.ofConv

-- Keep the unit's codomain canonical before composing with `Spec.mapMulEquiv`.
private def diagonalAffineUnit (X : Over (Spec (.of K))) :
    X ⟶ (Spec (.of (((algΓ (.of K)).obj X).unop))).asOver (Spec (.of K)) :=
  (algΓAlgSpecAdjunction (.of K)).unit.app X

-- Identify one application without unfolding the canonical target in a product.
private lemma diagonalAffineHomOfConv_eq_unit_comp
    (X : Over (Spec (.of K))) (A : Type u) [CommRing A] [Bialgebra K A]
    (φ : WithConv (A →ₐ[K] ((algΓ (.of K)).obj X).unop)) :
    diagonalAffineHomOfConv K X A φ =
      diagonalAffineUnit K X ≫
        Spec.mapMulEquiv (R := K) (S := A) (T := ((algΓ (.of K)).obj X).unop) φ := by
  exact (algΓAlgSpecAdjunction (.of K)).homEquiv_unit X
    (.op (CommAlgCat.of K A)) (CommAlgCat.ofHom φ.ofConv).op

-- The adjunction inverse is `Spec.map` precomposed with the adjunction unit.
-- Thus convolution multiplication becomes multiplication of scheme morphisms.
private lemma diagonalAffineHomOfConv_mul
    (X : Over (Spec (.of K))) (A : Type u) [CommRing A] [Bialgebra K A]
    (φ ψ : WithConv (A →ₐ[K] ((algΓ (.of K)).obj X).unop)) :
    diagonalAffineHomOfConv K X A (φ * ψ) =
      diagonalAffineHomOfConv K X A φ * diagonalAffineHomOfConv K X A ψ := by
  rw [diagonalAffineHomOfConv_eq_unit_comp, diagonalAffineHomOfConv_eq_unit_comp,
    diagonalAffineHomOfConv_eq_unit_comp, map_mul]
  exact MonObj.comp_mul (diagonalAffineUnit K X) _ _

private lemma multiplicativeGroupHomUnits_symm_mul
    (X : Over (Spec (.of K))) (a b : ((algΓ (.of K)).obj X).unopˣ) :
    (multiplicativeGroupHomUnits K X).symm (a * b) =
      (multiplicativeGroupHomUnits K X).symm a *
        (multiplicativeGroupHomUnits K X).symm b := by
  change diagonalAffineHomOfConv K X (multiplicativeGroupCoordinateRing K)
      (multiplicativeGroupMulEquivAlgHom K _ (a * b)) =
    diagonalAffineHomOfConv K X (multiplicativeGroupCoordinateRing K)
        (multiplicativeGroupMulEquivAlgHom K _ a) *
      diagonalAffineHomOfConv K X (multiplicativeGroupCoordinateRing K)
        (multiplicativeGroupMulEquivAlgHom K _ b)
  rw [map_mul, diagonalAffineHomOfConv_mul]

/-- The global unit of a product of maps to `Gₘ` is the product of their global units. -/
theorem multiplicativeGroupHomUnits_mul (X : Over (Spec (.of K)))
    (f g : X ⟶ (multiplicativeGroupScheme K).X) :
    multiplicativeGroupHomUnits K X (f * g) =
      multiplicativeGroupHomUnits K X f * multiplicativeGroupHomUnits K X g := by
  apply (multiplicativeGroupHomUnits K X).symm.injective
  rw [Equiv.symm_apply_apply, multiplicativeGroupHomUnits_symm_mul,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The constant unit map to `Gₘ` corresponds to the unit global section. -/
@[simp]
theorem multiplicativeGroupHomUnits_one (X : Over (Spec (.of K))) :
    multiplicativeGroupHomUnits K X (1 : X ⟶ (multiplicativeGroupScheme K).X) = 1 := by
  have h : multiplicativeGroupHomUnits K X 1 * multiplicativeGroupHomUnits K X 1 =
      multiplicativeGroupHomUnits K X 1 := by
    simpa only [one_mul] using
      (multiplicativeGroupHomUnits_mul K X (1 : X ⟶ (multiplicativeGroupScheme K).X) 1).symm
  exact mul_eq_left.mp h

/-- Composition with a projection reads the corresponding global unit,
even when the test scheme is not affine. -/
theorem diagonalGroupProjection_globalUnit (j : n) (X : Over (Spec (.of K)))
    (hom : X ⟶ (diagonalGroupScheme K n).X) :
    multiplicativeGroupHomUnits K X (hom ≫ (diagonalGroupProjection K n j).hom.hom) =
      diagonalGroupHomUnits K n X hom j := by
  have hcomp : affineSpecHomOverEquiv K X (multiplicativeGroupCoordinateRing K)
      (hom ≫ (diagonalGroupProjection K n j).hom.hom) =
      (affineSpecHomOverEquiv K X (DiagonalCoordinateRing.CoordinateRing K n) hom).comp
        (diagonalGroupProjectionCoordinateMap K n j) :=
    affineSpecHomOverEquiv_comp K X (DiagonalCoordinateRing.CoordinateRing K n)
      (multiplicativeGroupCoordinateRing K)
      (diagonalGroupProjectionCoordinateMap K n j) hom
  apply Units.ext
  change (((multiplicativeGroupMulEquivAlgHom K _).symm
      (WithConv.toConv (affineSpecHomOverEquiv K X (multiplicativeGroupCoordinateRing K)
        (hom ≫ (diagonalGroupProjection K n j).hom.hom))) :
        ((algΓ (.of K)).obj X).unopˣ) : ((algΓ (.of K)).obj X).unop) = _
  rw [← multiplicativeGroupMulEquivAlgHom_coordinate K _
    ((multiplicativeGroupMulEquivAlgHom K _).symm
      (WithConv.toConv (affineSpecHomOverEquiv K X (multiplicativeGroupCoordinateRing K)
        (hom ≫ (diagonalGroupProjection K n j).hom.hom))))]
  simp only [MulEquiv.apply_symm_apply]
  rw [hcomp, AlgHom.comp_apply,
    diagonalGroupProjection_coordinate]
  change (affineSpecHomOverEquiv K X (DiagonalCoordinateRing.CoordinateRing K n) hom)
      (quotient K n (matrix K n j j)) =
    ↑(Matrix.DiagonalGroup.unitsEquiv
      ((diagonalGroupMulEquivAlgHom K n _).symm
        (WithConv.toConv (affineSpecHomOverEquiv K X
          (DiagonalCoordinateRing.CoordinateRing K n) hom))) j)
  rw [Matrix.DiagonalGroup.unitsEquiv_apply_val,
    ← diagonalGroupMulEquivAlgHom_entry K n _
      ((diagonalGroupMulEquivAlgHom K n _).symm
        (WithConv.toConv (affineSpecHomOverEquiv K X
          (DiagonalCoordinateRing.CoordinateRing K n) hom))) j j]
  simp

/-- The genuine projection fan in group objects over the base. -/
def diagonalGroupProductFan : Limits.Fan (fun _ : n ↦ multiplicativeGroupScheme K) :=
  Limits.Fan.mk (diagonalGroupScheme K n) (diagonalGroupProjection K n)

/-- The underlying cone is universal over all schemes over `Spec K`. -/
def diagonalGroupProductFan_forget_isLimit :
    Limits.IsLimit ((Grp.forget (Over (Spec (.of K)))).mapCone
      (diagonalGroupProductFan K n)) := by
  change Limits.IsLimit (Limits.Fan.mk (diagonalGroupScheme K n).X
    (fun j : n ↦ (diagonalGroupProjection K n j).hom.hom))
  refine Limits.Fan.IsLimit.mk _ (fun cone ↦
    (diagonalGroupHomUnits K n cone.pt).symm
      (fun j ↦ multiplicativeGroupHomUnits K cone.pt (cone.proj j))) ?_ ?_
  · intro cone j
    apply (multiplicativeGroupHomUnits K cone.pt).injective
    change multiplicativeGroupHomUnits K cone.pt
      ((diagonalGroupHomUnits K n cone.pt).symm
        (fun j ↦ multiplicativeGroupHomUnits K cone.pt (cone.proj j)) ≫
          (diagonalGroupProjection K n j).hom.hom) =
        multiplicativeGroupHomUnits K cone.pt (cone.proj j)
    rw [diagonalGroupProjection_globalUnit]
    simp
  · intro cone morphism factor
    apply (diagonalGroupHomUnits K n cone.pt).injective
    funext j
    simp only [Equiv.apply_symm_apply]
    rw [← diagonalGroupProjection_globalUnit K n j cone.pt morphism]
    have hfac : morphism ≫ (diagonalGroupProjection K n j).hom.hom = cone.proj j :=
      factor j
    rw [hfac]

/-- The group-object forgetful functor reflects this product limit. -/
def diagonalGroupProductFan_isLimit : Limits.IsLimit (diagonalGroupProductFan K n) :=
  Limits.isLimitOfReflects (Grp.forget (Over (Spec (.of K))))
    (diagonalGroupProductFan_forget_isLimit K n)

/-- The finite categorical product of multiplicative group schemes over any
commutative base; compare Milne, *Algebraic Groups* (2017), §12.d (p. 234),
for the diagonal product over a field. -/
def diagonalGroupSchemeProductIso :
    diagonalGroupScheme K n ≅ (∏ᶜ fun _ : n ↦ multiplicativeGroupScheme K) :=
  (diagonalGroupProductFan_isLimit K n).conePointUniqueUpToIso
    (Limits.productIsProduct fun _ : n ↦ multiplicativeGroupScheme K)

@[simp] theorem diagonalGroupSchemeProductIso_hom_π (j : n) :
    (diagonalGroupSchemeProductIso K n).hom ≫
      Limits.Pi.π (fun _ : n ↦ multiplicativeGroupScheme K) j =
        diagonalGroupProjection K n j :=
  (diagonalGroupProductFan_isLimit K n).conePointUniqueUpToIso_hom_comp
    (Limits.productIsProduct fun _ : n ↦ multiplicativeGroupScheme K) ⟨j⟩

@[simp] theorem diagonalGroupSchemeProductIso_inv_projection (j : n) :
    (diagonalGroupSchemeProductIso K n).inv ≫ diagonalGroupProjection K n j =
      Limits.Pi.π (fun _ : n ↦ multiplicativeGroupScheme K) j :=
  (diagonalGroupProductFan_isLimit K n).conePointUniqueUpToIso_inv_comp
    (Limits.productIsProduct fun _ : n ↦ multiplicativeGroupScheme K) ⟨j⟩

/-- The empty diagonal group scheme is terminal over any commutative base. -/
def diagonalGroupSchemeEmptyIsTerminal :
    Limits.IsTerminal (diagonalGroupScheme K PEmpty.{u+1}) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (diagonalGroupProductFan K PEmpty.{u+1}))
    (diagonalGroupProductFan_isLimit K PEmpty.{u+1})

/-- The terminality statement specialized to the finite empty index type. -/
def diagonalGroupSchemeFin0IsTerminal (K : Type) [CommRing K] :
    Limits.IsTerminal (diagonalGroupScheme K (Fin 0)) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (diagonalGroupProductFan K (Fin 0)))
    (diagonalGroupProductFan_isLimit K (Fin 0))

end AlgebraicGeometry
