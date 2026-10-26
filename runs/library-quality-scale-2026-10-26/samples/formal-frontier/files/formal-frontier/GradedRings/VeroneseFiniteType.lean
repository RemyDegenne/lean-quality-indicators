/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.WeightedVeroneseGenerators
public import GradedRings.WeightedEvaluation
public import GradedRings.Veronese
public import Mathlib.RingTheory.GradedAlgebra.FiniteType

/-!
# Finite type of prescribed positive Veronese rings

A finite homogeneous generating family of any natural weights gives finite type for
every positive selected-component ring over its entire new degree-zero component.
In particular, this applies to any naturally graded algebra of finite type over
its original degree-zero ring. No positivity assumption on generator weights or
domain assumption on the ring is needed.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

namespace GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] Fintype.ofFinite in
/-- A finite homogeneous algebra generating family gives finite type for each
prescribed positive Veronese over its whole degree-zero ring. -/
theorem finiteType_of_finite_homogeneous_generators {ι : Type*} [Finite ι]
    (w : ι → ℕ) (x : ∀ i : ι, 𝒮 (w i))
    (hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤)
    (n : ℕ) (hn : 0 < n) :
    Algebra.FiniteType (component 𝒮 n 0) (VeroneseRing 𝒮 n) := by
  classical
  obtain ⟨T, hTdegree, hTgen⟩ :=
    MvPolynomial.exists_finset_weightedVeronese_generators (R := 𝒮 0) w n hn
  let e : MvPolynomial ι (𝒮 0) →ₐ[𝒮 0] S := MvPolynomial.aeval (fun i => (x i : S))
  let degree (p : T) : ℕ := (hTdegree p.1 p.2).choose
  have heval (p : T) : e p.1 ∈ 𝒮 (n * degree p) :=
    (hTdegree p.1 p.2).choose_spec.aeval_mem 𝒮 w x
  let lift (p : T) : VeroneseRing 𝒮 n :=
    (exists_component 𝒮 n (degree p) ⟨e p.1, heval p⟩).choose
  have hlift (p : T) : inclusion 𝒮 n (lift p) = e p.1 :=
    (exists_component 𝒮 n (degree p) ⟨e p.1, heval p⟩).choose_spec.2
  let U : Subalgebra (component 𝒮 n 0) (VeroneseRing 𝒮 n) :=
    Algebra.adjoin _ (Set.range lift)
  have hpoly {p : MvPolynomial ι (𝒮 0)}
      (hp : p ∈ Algebra.adjoin (𝒮 0) (T : Set (MvPolynomial ι (𝒮 0)))) :
      ∃ t : VeroneseRing 𝒮 n, t ∈ U ∧ inclusion 𝒮 n t = e p := by
    induction hp using Algebra.adjoin_induction with
    | mem p hp =>
        refine ⟨lift ⟨p, hp⟩, Algebra.subset_adjoin (Set.mem_range_self _), ?_⟩
        exact hlift ⟨p, hp⟩
    | algebraMap r =>
        let t : VeroneseRing 𝒮 n :=
          algebraMap (component 𝒮 n 0) (VeroneseRing 𝒮 n)
            ((zeroRingEquiv 𝒮 n hn).symm r)
        refine ⟨t, U.algebraMap_mem _, ?_⟩
        change inclusion 𝒮 n (((zeroRingEquiv 𝒮 n hn).symm r : component 𝒮 n 0) :
          VeroneseRing 𝒮 n) = e (algebraMap _ _ r)
        rw [← zeroRingEquiv_apply 𝒮 n hn]
        simp only [RingEquiv.apply_symm_apply, e, AlgHom.commutes,
          SetLike.GradeZero.algebraMap_apply]
    | add p q _ _ ihp ihq =>
        obtain ⟨t, ht, heq⟩ := ihp
        obtain ⟨s, hs, hsq⟩ := ihq
        refine ⟨t + s, U.add_mem ht hs, ?_⟩
        rw [map_add, heq, map_add, hsq]
    | mul p q _ _ ihp ihq =>
        obtain ⟨t, ht, heq⟩ := ihp
        obtain ⟨s, hs, hsq⟩ := ihq
        refine ⟨t * s, U.mul_mem ht hs, ?_⟩
        rw [map_mul, heq, map_mul, hsq]
  have htop : U = ⊤ := by
    apply top_unique
    intro t _
    have hall : ∀ t : VeroneseRing 𝒮 n, t ∈ U := by
      intro t
      induction t using DirectSum.induction_on with
      | zero => exact U.zero_mem
      | of j a =>
          obtain ⟨p, hp, heq⟩ := MvPolynomial.exists_isWeightedHomogeneous_aeval
            𝒮 w x hgen a.property
          obtain ⟨s, hs, hseval⟩ := hpoly (hTgen j p hp)
          have hsame : s = DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j a :=
            inclusion_injective 𝒮 n hn
              (hseval.trans (heq.trans (inclusion_of 𝒮 n j a).symm))
          exact hsame ▸ hs
      | add a b ha hb => exact U.add_mem ha hb
    exact hall t
  have hfinite : (Set.range lift).Finite := by
    have : Finite T := (Finset.finite_toSet T).to_subtype
    exact Set.finite_range lift
  exact ⟨Subalgebra.fg_def.mpr ⟨Set.range lift, hfinite, htop⟩⟩

/-- Every naturally graded algebra of finite type over its degree-zero ring
has a finite-type selected-component ring at each prescribed positive index. -/
theorem finiteType_of_finiteType [Algebra.FiniteType (𝒮 0) S]
    (n : ℕ) (hn : 0 < n) :
    Algebra.FiniteType (component 𝒮 n 0) (VeroneseRing 𝒮 n) := by
  classical
  obtain ⟨F, hF, hdegree⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒮
  let w (i : F) : ℕ := (hdegree i.1 i.2).choose
  let x (i : F) : 𝒮 (w i) := ⟨i.1, (hdegree i.1 i.2).choose_spec.2⟩
  have hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i : F => (x i : S))) = ⊤ := by
    have heq : Set.range (fun i : F => (x i : S)) = (F : Set S) := by
      apply Set.ext
      intro s
      constructor
      · rintro ⟨i, rfl⟩
        exact i.2
      · intro hs
        exact ⟨⟨s, hs⟩, rfl⟩
    rw [heq]
    exact hF
  exact finiteType_of_finite_homogeneous_generators 𝒮 w x hgen n hn

end GradedRing.Veronese
