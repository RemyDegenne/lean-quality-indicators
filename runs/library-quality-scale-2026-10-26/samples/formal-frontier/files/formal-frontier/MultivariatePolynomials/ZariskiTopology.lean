/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.QuotientClosedPoints
import Mathlib.Topology.Bases

/-!
# The polynomial Zariski topology on field-valued coordinates

`ZariskiSpace K σ` is a wrapped tuple of coordinates with the topology induced by
its evaluation point in the prime spectrum of `MvPolynomial σ K`. Its closed
sets are exactly polynomial zero loci, independently of a topology on `K` or
on the function type `σ → K`. Polynomial substitutions give continuous maps.
The evaluation map from any zero locus into the closed-point subspace of its
quotient spectrum is an embedding; for an algebraically closed field and
finitely many variables, the existing coordinate equivalence is a homeomorphism.

The closed-point subspace carries its inherited spectrum topology rather than
a topology declared discrete by default; in particular cases it can be discrete.
The homeomorphism applies to arbitrary ideals, including
the unit ideal and nonradical ideals. Over an arbitrary field the evaluation
map need not be surjective onto the quotient's closed points.

## References

* Mathlib, `Mathlib.RingTheory.Nullstellensatz` for `zeroLocus`,
  `vanishingIdeal` and `pointToPoint`; `Mathlib.RingTheory.Spectrum.Prime.Topology`
  for the spectrum topology; and `Mathlib.Algebra.MvPolynomial.Comap` for
  polynomial substitution.
* `MultivariatePolynomials.EvaluationIdeal` and
  `MultivariatePolynomials.QuotientClosedPoints` for the evaluation kernels,
  quotient closed points and their coordinate equivalence.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

/-- Field-valued coordinate tuples, separated from any topology on the function type. -/
structure ZariskiSpace (K : Type u) (σ : Type v) where
  toFun : σ → K

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

instance : CoeFun (ZariskiSpace K σ) (fun _ => σ → K) where
  coe := ZariskiSpace.toFun

/-- The underlying coordinates of a Zariski tuple. -/
def coordinatesEquiv : ZariskiSpace K σ ≃ (σ → K) where
  toFun := ZariskiSpace.toFun
  invFun := ZariskiSpace.mk
  left_inv := by intro ⟨_⟩; rfl
  right_inv := by intro _; rfl

@[simp] theorem coordinatesEquiv_apply (x : ZariskiSpace K σ) :
    coordinatesEquiv x = x.toFun := rfl

@[simp] theorem coordinatesEquiv_symm_apply (x : σ → K) :
    (coordinatesEquiv (K := K) (σ := σ)).symm x = ⟨x⟩ := rfl

@[simp] theorem mk_apply (x : σ → K) (i : σ) : (⟨x⟩ : ZariskiSpace K σ) i = x i := rfl

/-- Two Zariski tuples agree if all their coordinates agree. -/
@[ext] theorem ext {x y : ZariskiSpace K σ} (h : ∀ i, x i = y i) : x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      congr 1
      funext i
      exact h i

variable [Field K]

instance : TopologicalSpace (ZariskiSpace K σ) :=
  TopologicalSpace.induced (fun x : ZariskiSpace K σ =>
    MvPolynomial.pointToPoint (k := K) x.toFun) inferInstance

/-- The tuples annihilating every polynomial in an ideal. -/
def zeroLocus (I : Ideal (MvPolynomial σ K)) : Set (ZariskiSpace K σ) :=
  {x | x.toFun ∈ MvPolynomial.zeroLocus K I}

@[simp] theorem mem_zeroLocus {I : Ideal (MvPolynomial σ K)} {x : ZariskiSpace K σ} :
    x ∈ zeroLocus I ↔ x.toFun ∈ MvPolynomial.zeroLocus K I := Iff.rfl

/-- The basic open set where a polynomial does not vanish. -/
def basicOpen (p : MvPolynomial σ K) : Set (ZariskiSpace K σ) :=
  {x | aeval x.toFun p ≠ 0}

@[simp] theorem mem_basicOpen {p : MvPolynomial σ K} {x : ZariskiSpace K σ} :
    x ∈ basicOpen p ↔ aeval x.toFun p ≠ 0 := Iff.rfl

/-- The evaluation point of a field-valued tuple in the polynomial prime spectrum. -/
def pointToPoint (x : ZariskiSpace K σ) : PrimeSpectrum (MvPolynomial σ K) :=
  MvPolynomial.pointToPoint (k := K) x.toFun

@[simp] theorem pointToPoint_asIdeal (x : ZariskiSpace K σ) :
    (pointToPoint x).asIdeal = MvPolynomial.vanishingIdeal K {x.toFun} := rfl

/-- Zero-locus membership is detected by the evaluation prime. -/
theorem mem_zeroLocus_iff_mem_spectrum_zeroLocus
    (I : Ideal (MvPolynomial σ K)) (x : ZariskiSpace K σ) :
    x ∈ zeroLocus I ↔ pointToPoint x ∈ PrimeSpectrum.zeroLocus I := by
  change (∀ p ∈ I, aeval x.toFun p = 0) ↔
    I ≤ MvPolynomial.vanishingIdeal K {x.toFun}
  simp only [SetLike.le_def, MvPolynomial.mem_vanishingIdeal_singleton_iff]

/-- Polynomial basic opens are pulled back from the spectrum. -/
theorem basicOpen_eq_preimage (p : MvPolynomial σ K) :
    basicOpen p = (pointToPoint (K := K) (σ := σ)) ⁻¹'
      (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial σ K))) := by
  ext x
  change aeval x.toFun p ≠ 0 ↔
    p ∉ MvPolynomial.vanishingIdeal K {x.toFun}
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x.toFun p).not.symm

/-- A subset is closed precisely when it is the common zero locus of a polynomial ideal. -/
theorem isClosed_iff (Z : Set (ZariskiSpace K σ)) :
    IsClosed Z ↔ ∃ I : Ideal (MvPolynomial σ K), Z = zeroLocus I := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨S, hS, hZS⟩
    obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal S).mp hS
    exact ⟨I, hZS.symm.trans (Set.ext fun x =>
      (mem_zeroLocus_iff_mem_spectrum_zeroLocus I x).symm)⟩
  · rintro ⟨I, rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus I,
      (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mpr ⟨I, rfl⟩,
      Set.ext fun x => (mem_zeroLocus_iff_mem_spectrum_zeroLocus I x).symm⟩

/-- Every polynomial zero locus is closed. -/
theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ K)) :
    IsClosed (zeroLocus I) := (isClosed_iff _).2 ⟨I, rfl⟩

/-- A subset is open precisely when its complement is a polynomial zero locus. -/
theorem isOpen_iff (U : Set (ZariskiSpace K σ)) :
    IsOpen U ↔ ∃ I : Ideal (MvPolynomial σ K), Uᶜ = zeroLocus I := by
  rw [← isClosed_compl_iff]
  exact isClosed_iff Uᶜ

/-- The nonvanishing set of a polynomial is open. -/
theorem isOpen_basicOpen (p : MvPolynomial σ K) : IsOpen (basicOpen p) := by
  rw [basicOpen_eq_preimage]
  exact (PrimeSpectrum.isOpen_basicOpen).preimage
    ((Topology.IsInducing.induced (pointToPoint (K := K) (σ := σ))).continuous)

/-- Basic polynomial nonvanishing sets form a basis of the coordinate topology. -/
theorem isTopologicalBasis_basicOpen :
    TopologicalSpace.IsTopologicalBasis
      (Set.range (basicOpen (K := K) (σ := σ))) := by
  have hSets : Set.range (basicOpen (K := K) (σ := σ)) =
      (Set.preimage (pointToPoint (K := K) (σ := σ))) ''
        Set.range (fun p : MvPolynomial σ K =>
          (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial σ K)))) := by
    ext U
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(PrimeSpectrum.basicOpen p : Set _), ⟨p, rfl⟩,
        (basicOpen_eq_preimage p).symm⟩
    · rintro ⟨S, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, basicOpen_eq_preimage p⟩
  rw [hSets]
  exact (Topology.IsInducing.induced (pointToPoint (K := K) (σ := σ))).isTopologicalBasis
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := MvPolynomial σ K))

/-- Evaluation embeds field-valued coordinates in the polynomial prime spectrum. -/
theorem isEmbedding_pointToPoint : Topology.IsEmbedding (pointToPoint (K := K) (σ := σ)) := by
  apply Topology.IsEmbedding.induced
  intro x y h
  apply ext
  intro i
  have hIdeal := congrArg PrimeSpectrum.asIdeal h
  have hmem : (X i - C (x i)) ∈ (pointToPoint x).asIdeal := by
    rw [pointToPoint_asIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [hIdeal, pointToPoint_asIdeal,
    MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  have heq : y i = x i := by
    simpa only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_self_apply,
      sub_eq_zero] using hmem
  exact heq.symm

/-- The contravariant coordinate map induced by polynomial substitution. -/
def substitution {τ : Type w}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) :
    ZariskiSpace K τ → ZariskiSpace K σ :=
  fun x => ⟨MvPolynomial.comap f x.toFun⟩

@[simp] theorem substitution_apply {τ : Type w}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (x : ZariskiSpace K τ) (i : σ) :
    substitution f x i = aeval x.toFun (f (X i)) :=
  MvPolynomial.comap_apply f x.toFun i

@[simp] theorem substitution_id :
    substitution (AlgHom.id K (MvPolynomial σ K)) = id := by
  funext x
  apply ext
  intro i
  exact congrFun (MvPolynomial.comap_id_apply x.toFun) i

/-- Substitution of a composite algebra map composes the coordinate maps in reverse. -/
theorem substitution_comp {τ : Type w} {υ : Type*}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (g : MvPolynomial τ K →ₐ[K] MvPolynomial υ K)
    (x : ZariskiSpace K υ) :
    substitution (g.comp f) x = substitution f (substitution g x) := by
  apply ext
  intro i
  exact congrFun (MvPolynomial.comap_comp_apply f g x.toFun) i

/-- Polynomial substitution is continuous in the polynomial Zariski topologies. -/
theorem continuous_substitution {τ : Type w}
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) :
    Continuous (substitution f) := by
  have hcomp : (pointToPoint (K := K) (σ := σ)) ∘ substitution f =
      (PrimeSpectrum.comap f.toRingHom) ∘ (pointToPoint (K := K) (σ := τ)) := by
    funext x
    exact (MvPolynomial.pointToPoint_comap_self f x.toFun).symm
  apply (isEmbedding_pointToPoint (K := K) (σ := σ)).continuous_iff.mpr
  rw [hcomp]
  exact (PrimeSpectrum.continuous_comap f.toRingHom).comp
    (isEmbedding_pointToPoint (K := K) (σ := τ)).continuous

/-- The wrapped zero locus agrees with Mathlib's tuple zero locus as a set of points. -/
def zeroLocusEquiv (I : Ideal (MvPolynomial σ K)) :
    zeroLocus I ≃ MvPolynomial.zeroLocus K I where
  toFun := fun x => ⟨x.val.toFun, x.property⟩
  invFun := fun x => ⟨⟨x.val⟩, x.property⟩
  left_inv := by intro ⟨⟨_⟩, _⟩; rfl
  right_inv := by intro ⟨_, _⟩; rfl

/-- The existing quotient evaluation closed point of a tuple in a zero locus. -/
def zeroLocusClosedPoint (I : Ideal (MvPolynomial σ K)) (x : zeroLocus I) :
    closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)) :=
  MvPolynomial.zeroLocusClosedPoint I (zeroLocusEquiv I x)

/-- Quotient polynomial membership at an evaluation closed point is vanishing. -/
theorem zeroLocusClosedPoint_mem_iff (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus I) (p : MvPolynomial σ K) :
    Ideal.Quotient.mkₐ K I p ∈ (zeroLocusClosedPoint I x).val.asIdeal ↔
      aeval x.val.toFun p = 0 :=
  MvPolynomial.zeroLocusClosedPoint_mem_iff I (zeroLocusEquiv I x) p

/-- Every polynomial zero locus embeds in the closed-point subspace of its quotient
prime spectrum, without finiteness or algebraic closure assumptions. -/
theorem isEmbedding_zeroLocusClosedPoint (I : Ideal (MvPolynomial σ K)) :
    Topology.IsEmbedding (zeroLocusClosedPoint I) := by
  have hcomp : (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ∘
      (fun x : zeroLocus I => (zeroLocusClosedPoint I x).val) =
        (pointToPoint (K := K) (σ := σ)) ∘ (fun x : zeroLocus I => x.val) := by
    funext x
    apply PrimeSpectrum.ext
    ext p
    change (Ideal.Quotient.mkₐ K I p) ∈ (zeroLocusClosedPoint I x).val.asIdeal ↔
      p ∈ MvPolynomial.vanishingIdeal K {x.val.toFun}
    rw [zeroLocusClosedPoint_mem_iff, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  have hpoint : Topology.IsEmbedding
      ((pointToPoint (K := K) (σ := σ)) ∘ (fun x : zeroLocus I => x.val)) :=
    (isEmbedding_pointToPoint (K := K) (σ := σ)).comp Topology.IsEmbedding.subtypeVal
  have hquotient : Topology.IsEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    PrimeSpectrum.isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hval : Topology.IsEmbedding
      (fun x : zeroLocus I => (zeroLocusClosedPoint I x).val) :=
    hquotient.of_comp_iff.mp (by simpa only [hcomp] using hpoint)
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hval

variable [IsAlgClosed K] [Finite σ]

/-- The original coordinate equivalence, restricted to wrapped Zariski tuples. -/
def zeroLocusEquivClosedPoints (I : Ideal (MvPolynomial σ K)) :
    zeroLocus I ≃ closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)) :=
  (zeroLocusEquiv I).trans (MvPolynomial.zeroLocusEquivClosedPoints I)

/-- The coordinate equivalence is a homeomorphism to the inherited closed-point
subspace of the quotient prime spectrum, including nonreduced quotients. -/
def zeroLocusHomeomorphClosedPoints (I : Ideal (MvPolynomial σ K)) :
    zeroLocus I ≃ₜ closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)) where
  toEquiv := zeroLocusEquivClosedPoints I
  continuous_toFun := (isEmbedding_zeroLocusClosedPoint I).continuous
  continuous_invFun :=
    ((zeroLocusEquivClosedPoints I).toHomeomorphOfIsInducing
      (isEmbedding_zeroLocusClosedPoint I).isInducing).continuous_invFun

/-- The homeomorphism has the original coordinate equivalence as its underlying map. -/
theorem zeroLocusHomeomorphClosedPoints_toEquiv (I : Ideal (MvPolynomial σ K)) :
    (zeroLocusHomeomorphClosedPoints I).toEquiv = zeroLocusEquivClosedPoints I := rfl

@[simp] theorem zeroLocusHomeomorphClosedPoints_apply
    (I : Ideal (MvPolynomial σ K)) (x : zeroLocus I) :
    zeroLocusHomeomorphClosedPoints I x = zeroLocusClosedPoint I x := rfl

/-- Forgetting closedness gives the original quotient-spectrum evaluation point. -/
@[simp] theorem zeroLocusHomeomorphClosedPoints_val
    (I : Ideal (MvPolynomial σ K)) (x : zeroLocus I) :
    (zeroLocusHomeomorphClosedPoints I x).val =
      (MvPolynomial.zeroLocusEquivClosedPoints I (zeroLocusEquiv I x)).val := rfl

/-- The prime underlying the homeomorphism is the descended evaluation kernel. -/
theorem zeroLocusHomeomorphClosedPoints_asIdeal
    (I : Ideal (MvPolynomial σ K)) (x : zeroLocus I) :
    (zeroLocusHomeomorphClosedPoints I x).val.asIdeal =
      RingHom.ker (MvPolynomial.zeroLocusQuotientEval I (zeroLocusEquiv I x)).toRingHom := by
  simpa only [zeroLocusHomeomorphClosedPoints_apply, zeroLocusClosedPoint] using
    MvPolynomial.zeroLocusClosedPoint_asIdeal I (zeroLocusEquiv I x)

@[simp] theorem zeroLocusHomeomorphClosedPoints_symm_apply
    (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) :
    (zeroLocusHomeomorphClosedPoints I).symm x =
      (zeroLocusEquiv I).symm ((MvPolynomial.zeroLocusEquivClosedPoints I).symm x) := rfl

end ZariskiSpace

end MvPolynomial
