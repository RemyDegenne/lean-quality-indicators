/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import SchemeProperties.GlobalSections.Field

/-!
# Global sections and morphisms to affine schemes

Precomposition by a morphism inducing an isomorphism on global sections is bijective
on morphisms into any affine scheme. The source and intermediate schemes are arbitrary.

A reduced connected scheme universally closed over a field has a field of global
sections. For a reduced preconnected scheme with a rational section, evaluation at
that section identifies the global sections with the base field. Consequently,
every morphism to an affine scheme factors through the rational section. Neither
finite type nor separatedness of the source is required.

For example, a projective line over a field has the same global sections as its
base, although it is not affine and its structure map is not an isomorphism.
The rational-section hypothesis rules out the spectrum of a nontrivial finite
field extension: that scheme is proper and integral but has the larger field
as its ring of global sections. Reducedness is substantive as well: the finite
connected scheme of dual numbers has a rational point but nonreduced global
sections.

## References

* J. S. Milne, *Abelian Varieties*, Chapter I, Theorem 1.1 (printed pages 8–9),
  for the affine-target constancy step in rigidity. The result here concerns the
  reduced preconnected pointed case and allows universally closed, rather than
  proper, sources.
* Mathlib, `AlgebraicGeometry.isField_of_universallyClosed`, for the field of
  global sections in the integral case, and `AlgebraicGeometry.ext_of_isAffine`,
  for affine-target morphisms determined by their maps on global sections.
* Minimal Primes, for the integral dimension bound and the reduced
  zero-dimensional field criterion used in `SchemeProperties.GlobalSections.Field`.
* Mathlib, `AlgebraicGeometry.ΓSpec.adjunction`, for the correspondence between
  morphisms to spectra and homomorphisms of rings of global sections, and
  `CategoryTheory.Adjunction.map_comp_bijective_iff`, for transporting
  precomposition bijectivity across an adjunction.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {K : Type u} [Field K] {X Y S : Scheme.{u}}

/-- A morphism inducing an isomorphism on global sections induces a bijection on
morphisms to every affine target, by precomposition. No section of the morphism is
required. -/
lemma precomp_bijective_of_isIso_appTop {T : Scheme.{u}}
    (p : X ⟶ S) [IsIso p.appTop] [IsAffine T] :
    Function.Bijective (fun h : S ⟶ T ↦ p ≫ h) := by
  have : IsIso (Scheme.Γ.rightOp.map p) := by
    simpa only [Functor.rightOp_obj, Scheme.Γ_obj_op, Functor.rightOp_map, Scheme.Γ_map_op] using
      (CategoryTheory.isIso_op p.appTop)
  have hSpec : Function.Bijective
      (fun h : S ⟶ Spec Γ(T, ⊤) ↦ p ≫ h) := by
    apply (ΓSpec.adjunction.map_comp_bijective_iff p (Opposite.op Γ(T, ⊤))).mp
    exact ((asIso (Scheme.Γ.rightOp.map p)).symm.homFromEquiv).bijective
  apply (Function.Bijective.of_comp_iff'
    (T.isoSpec.homToEquiv (Z := X)).bijective _).mp
  simpa only [Function.comp_def, Iso.homToEquiv, Equiv.coe_fn_mk, Category.assoc] using
    hSpec.comp (T.isoSpec.homToEquiv (Z := S)).bijective

/-- When a morphism is an isomorphism on global sections, the map on global sections
induced by any section is its inverse. -/
lemma inv_appTop_eq_appTop_of_section
    (f : X ⟶ S) [IsIso f.appTop]
    (p : S ⟶ X) (hp : p ≫ f = 𝟙 _) : inv f.appTop = p.appTop := by
  apply (cancel_epi f.appTop).mp
  rw [IsIso.hom_inv_id, ← comp_appTop, hp]
  simp

/-- If a morphism is an isomorphism on global sections, every morphism to an
independent affine target factors through any section. The base scheme is arbitrary. -/
lemma eq_comp_section_of_isIso_appTop
    (f : X ⟶ S) [IsIso f.appTop]
    (p : S ⟶ X) (hp : p ≫ f = 𝟙 _)
    [IsAffine Y] (g : X ⟶ Y) : g = f ≫ p ≫ g := by
  apply ext_of_isAffine
  simp only [comp_appTop, Category.assoc, ← inv_appTop_eq_appTop_of_section f p hp,
    IsIso.inv_hom_id, Category.comp_id]

/-- For an integral scheme universally closed over a field, a given section makes
its map on global sections an isomorphism. -/
lemma isIso_appTop_of_universallyClosed_of_section
    (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) : IsIso f.appTop := by
  exact isIso_appTop_of_isReduced_of_universallyClosed_of_section f p hp

/-- Every morphism from a pointed reduced preconnected scheme universally closed over
a field to an affine scheme is constant at the image of its rational point. This
generalizes the integral pointed case of affine-target constancy used in Milne,
*Abelian Varieties*, Chapter I, Theorem 1.1, without finite-type or separatedness
assumptions on the source. -/
lemma eq_comp_section_of_isReduced_of_universallyClosed
    (f : X ⟶ Spec (.of K)) [IsReduced X] [PreconnectedSpace X] [UniversallyClosed f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    [IsAffine Y] (g : X ⟶ Y) : g = f ≫ p ≫ g := by
  let := isIso_appTop_of_isReduced_of_universallyClosed_of_section f p hp
  exact eq_comp_section_of_isIso_appTop f p hp g

/-- Every morphism from a pointed integral scheme universally closed over a field
to an affine scheme is constant at the image of its rational point. -/
lemma eq_comp_section_of_universallyClosed
    (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    [IsAffine Y] (g : X ⟶ Y) : g = f ≫ p ≫ g := by
  exact eq_comp_section_of_isReduced_of_universallyClosed f p hp g

end AlgebraicGeometry.Scheme.Hom
