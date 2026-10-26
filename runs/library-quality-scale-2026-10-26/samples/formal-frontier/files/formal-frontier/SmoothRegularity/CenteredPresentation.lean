/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.AlgClosed
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Finsupp.Weight

/-!
# Presentations centred at a closed point

This file constructs finite generators and presentations of a finite-type
algebra over an algebraically closed field such that every distinguished
generator belongs to a chosen maximal ideal.

Starting from arbitrary finite generators, subtract from each generator the
scalar represented by its residue.  The adjusted elements lie in the maximal
ideal and still generate the algebra, since the original elements are recovered
by adding those scalars back.  Finite presentation then follows because the
base field is Noetherian.
-/

public section

namespace Ideal

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

/-- A finite-type algebra over an algebraically closed field has a finite
family of algebra generators contained in any chosen maximal ideal. -/
theorem exists_generators_mem_of_isAlgClosed (m : Ideal S) [m.IsMaximal] :
    ∃ (n : ℕ) (P : Algebra.Generators K S (Fin n)), ∀ i, P.val i ∈ m := by
  obtain ⟨n, ⟨P⟩⟩ :=
    (Algebra.FiniteType.iff_exists_generators (R := K) (S := S)).mp inferInstance
  let e := m.residueFieldAlgEquivOfIsAlgClosed (K := K)
  let val : Fin n → S := fun i ↦
    P.val i - algebraMap K S (e (algebraMap S m.ResidueField (P.val i)))
  have hval (i : Fin n) : val i ∈ m := by
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simp only [val, map_sub, sub_eq_zero]
    rw [← IsScalarTower.algebraMap_apply K S m.ResidueField]
    exact e.injective (by simp)
  have hP : Algebra.adjoin K (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact P.aeval_val_surjective
  have hval_top : Algebra.adjoin K (Set.range val) = ⊤ := by
    apply top_unique
    rw [← hP]
    apply Algebra.adjoin_le
    rintro x ⟨i, rfl⟩
    have hi : val i ∈ Algebra.adjoin K (Set.range val) :=
      Algebra.subset_adjoin ⟨i, rfl⟩
    have hc : algebraMap K S (e (algebraMap S m.ResidueField (P.val i))) ∈
        Algebra.adjoin K (Set.range val) := Subalgebra.algebraMap_mem _ _
    simpa [val] using (Algebra.adjoin K (Set.range val)).add_mem hi hc
  refine ⟨n, Algebra.Generators.ofSurjective val ?_, ?_⟩
  · rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  · exact hval

omit [Algebra.FiniteType K S] in
/-- Over an algebraically closed field, if every distinguished generator maps
into a maximal ideal, its preimage in the polynomial ring is the ideal generated
by all variables. The finite-type instance is supplied by the generators. -/
theorem comap_aeval_eq_idealOfVars_of_generators_mem {n : ℕ}
    (m : Ideal S) [m.IsMaximal] (P : Algebra.Generators K S (Fin n))
    (hP : ∀ i, P.val i ∈ m) :
    m.comap (MvPolynomial.aeval P.val) =
      MvPolynomial.idealOfVars (Fin n) K := by
  let _ : Algebra.FiniteType K S := P.finiteType
  apply le_antisymm
  · intro p hp
    simpa only [pow_one] using
      (MvPolynomial.mem_pow_idealOfVars_iff' (n := 1) p).2 (by
        intro x hx
        have hx0 : x = 0 := by
          rw [Nat.lt_one_iff] at hx
          exact (Finsupp.degree_eq_zero_iff x).mp hx
        subst x
        let e := m.residueFieldAlgEquivOfIsAlgClosed (K := K)
        have hz : algebraMap S m.ResidueField (MvPolynomial.aeval P.val p) = 0 := by
          rw [Ideal.algebraMap_residueField_eq_zero]
          exact hp
        have hvar (i : Fin n) :
            e (algebraMap S m.ResidueField (P.val i)) = 0 := by
          rw [← map_zero e]
          congr 1
          rw [Ideal.algebraMap_residueField_eq_zero]
          exact hP i
        let q : S →ₐ[K] m.ResidueField := IsScalarTower.toAlgHom K S m.ResidueField
        have hcomp : e.toAlgHom.comp (q.comp (MvPolynomial.aeval P.val)) =
            MvPolynomial.aeval (fun _ : Fin n ↦ (0 : K)) := by
          ext i
          simpa [q] using hvar i
        have heval : e (algebraMap S m.ResidueField (MvPolynomial.aeval P.val p)) =
            algebraMap K K (MvPolynomial.constantCoeff p) := by
          have := DFunLike.congr_fun hcomp p
          simpa [q, MvPolynomial.aeval_zero] using this
        rw [hz, map_zero] at heval
        change MvPolynomial.constantCoeff p = 0
        exact heval.symm)
  · rw [MvPolynomial.idealOfVars, Ideal.span_le, Set.range_subset_iff]
    intro i
    simpa using hP i

/-- A finite-type algebra over an algebraically closed field has a finite
presentation whose distinguished generators belong to any chosen maximal
ideal. -/
theorem exists_presentation_mem_of_isAlgClosed (m : Ideal S) [m.IsMaximal] :
    ∃ (n r : ℕ) (P : Algebra.Presentation K S (Fin n) (Fin r)),
      ∀ i, P.val i ∈ m := by
  obtain ⟨n, P, hP⟩ := m.exists_generators_mem_of_isAlgClosed (K := K)
  let _ : Algebra.FinitePresentation K S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let H := Submodule.fg_iff_exists_fin_generating_family.mp
    P.fg_ker_of_finitePresentation
  let r := H.choose
  let relation : Fin r → P.Ring := H.choose_spec.choose
  have hrelation : Ideal.span (Set.range relation) = P.ker :=
    H.choose_spec.choose_spec
  let Q : Algebra.Presentation K S (Fin n) (Fin r) :=
    { toGenerators := P
      relation := relation
      span_range_relation_eq_ker := hrelation }
  exact ⟨n, r, Q, hP⟩

end Ideal
