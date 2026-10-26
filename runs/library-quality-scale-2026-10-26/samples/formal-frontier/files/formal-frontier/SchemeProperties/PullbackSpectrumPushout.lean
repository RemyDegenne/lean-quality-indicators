/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PullbackOpenImmersion
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# The prime spectrum of a surjective ring pullback

If `α : A →+* C` is surjective and `β : B →+* C` is arbitrary, the whole prime
spectrum of `RingHom.pullback α β` is the topological pushout of the spectra
of `A` and `B` over the spectrum of `C`. All four spectra can be lifted to a
common universe without restricting the universes of the rings or of target
topological spaces. The result concerns topological spaces, not a pushout of schemes.

The complementary open charts in `SchemeProperties.PullbackOpenImmersion` cover
only part of the spectrum; the topological pushout also includes the closed locus.

## References

- Fujiwara–Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2), for
  motivation; the original text is not used for the proof.
- Schröer, *A simple proof for Hochster's Theorem*, for the finite-space context.
- The finite-space ring realization exposition, for the direct spectrum-pushout
  argument (rather than an assertion about the proof in either cited work).
- Mathlib's ring pullback, prime-spectrum topology, and `TopCat` colimit APIs.
- `SchemeProperties.PullbackOpenImmersion`, for complementary open charts.
-/

@[expose] public section

universe u v w z uT uA uB uC uX

open CategoryTheory CategoryTheory.Limits

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The map on spectra induced by a ring homomorphism, with the domain and
codomain lifted to a common universe. The lift absorbs the universes of both
rings, so it also works when their carriers live in different universes. -/
def comapULift (f : R →+* S) :
    (TopCat.uliftFunctor.{max u v w}).obj (TopCat.of (PrimeSpectrum S)) ⟶
      (TopCat.uliftFunctor.{max u v w}).obj (TopCat.of (PrimeSpectrum R)) :=
  TopCat.ofHom ⟨ULift.map (comap f), continuous_uliftMap _ (continuous_comap f)⟩

@[simp] theorem comapULift_apply (f : R →+* S)
    (x : (TopCat.uliftFunctor.{max u v w}).obj (TopCat.of (PrimeSpectrum S))) :
    comapULift.{u, v, w} f x = ⟨comap f x.down⟩ := rfl

/-- The lifted spectrum map of an identity is the identity. -/
@[simp] theorem comapULift_id (R : Type u) [CommRing R] :
    comapULift.{u, u, w} (RingHom.id R) =
      𝟙 ((TopCat.uliftFunctor.{max u w}).obj (TopCat.of (PrimeSpectrum R))) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  simp [comapULift_apply, comap_id]

/-- Lifted spectrum maps reverse composition of ring homomorphisms. -/
theorem comapULift_comp {T : Type uT} [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    comapULift.{u, uT, max u v uT z} (g.comp f) =
      comapULift.{v, uT, max u v uT z} g ≫
        comapULift.{u, v, max u v uT z} f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  exact comap_comp_apply f g x.down

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing A] [CommRing B] [CommRing C]

/-- The four lifted spectrum maps in a ring-pullback square commute. -/
theorem comapULift_pullback_comm (α : A →+* C) (β : B →+* C) :
    comapULift.{uA, uC, max uA uB uC w} α ≫
        comapULift.{max uA uB, uA, max uA uB uC w} (α.pullbackFst β) =
      comapULift.{uB, uC, max uA uB uC w} β ≫
        comapULift.{max uA uB, uB, max uA uB uC w} (α.pullbackSnd β) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change comap (α.pullbackFst β) (comap α x.down) =
    comap (α.pullbackSnd β) (comap β x.down)
  rw [← comap_comp_apply, ← comap_comp_apply, RingHom.pullback_comm_sq]

private theorem mem_range_comap_pullbackFst_of_not_ker (α : A →+* C) (β : B →+* C)
    (p : PrimeSpectrum (α.pullback β))
    (h : ¬ RingHom.ker (α.pullbackSnd β) ≤ p.asIdeal) :
    p ∈ Set.range (comap (α.pullbackFst β)) := by
  obtain ⟨i, hi, hip⟩ := SetLike.not_le_iff_exists.mp h
  let lift (a : A) : α.pullback β :=
    ⟨(i.1.1 * a, 0), by
      have hαi : α i.1.1 = 0 := by
        have hi' : i.1.2 = 0 := hi
        calc
          α i.1.1 = β i.1.2 := i.2
          _ = 0 := by simp [hi']
      simp [map_mul, hαi]⟩
  have hlift (d : α.pullback β) : lift ((α.pullbackFst β) d) = i * d := by
    apply Subtype.ext
    apply Prod.ext <;> simp [lift, show i.1.2 = 0 from hi]
  have hmul (a b : A) : i * lift (a * b) = lift a * lift b := by
    apply Subtype.ext
    apply Prod.ext
    · change i.1.1 * (i.1.1 * (a * b)) = (i.1.1 * a) * (i.1.1 * b)
      ac_rfl
    · simp [lift, show i.1.2 = 0 from hi]
  let J : Ideal A :=
    { carrier := {a | lift a ∈ p.asIdeal}
      zero_mem' := by
        have hz : lift 0 = 0 := by
          apply Subtype.ext
          apply Prod.ext <;> simp [lift]
        simp [hz]
      add_mem' := by
        intro a b ha hb
        change lift a ∈ p.asIdeal at ha
        change lift b ∈ p.asIdeal at hb
        have hadd : lift (a + b) = lift a + lift b := by
          apply Subtype.ext
          apply Prod.ext <;> simp [lift, mul_add]
        change lift (a + b) ∈ p.asIdeal
        rw [hadd]
        exact p.asIdeal.add_mem ha hb
      smul_mem' := by
        intro a b hb
        change lift (a * b) ∈ p.asIdeal
        have hprod : i * lift (a * b) ∈ p.asIdeal := by
          rw [hmul]
          exact p.asIdeal.mul_mem_left (lift a) hb
        exact (p.isPrime.mem_or_mem hprod).resolve_left hip }
  have hmap : Ideal.map (α.pullbackFst β) p.asIdeal ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    change lift ((α.pullbackFst β) d) ∈ p.asIdeal
    rw [hlift]
    exact p.asIdeal.mul_mem_left i hd
  have hcomap : (Ideal.map (α.pullbackFst β) p.asIdeal).comap
      (α.pullbackFst β) ≤ p.asIdeal := by
    intro d hd
    have hd' : lift ((α.pullbackFst β) d) ∈ p.asIdeal :=
      hmap hd
    rw [hlift] at hd'
    exact (p.isPrime.mem_or_mem hd').resolve_left hip
  apply (mem_range_comap_iff (α.pullbackFst β)).mpr
  exact le_antisymm hcomap Ideal.le_comap_map

private theorem range_comap_pullback_cover (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) (p : PrimeSpectrum (α.pullback β)) :
    p ∈ Set.range (comap (α.pullbackFst β)) ∪
      Set.range (comap (α.pullbackSnd β)) := by
  by_cases h : RingHom.ker (α.pullbackSnd β) ≤ p.asIdeal
  · right
    rw [range_comap_of_surjective _ _
      (RingHom.surjective_pullbackSnd_of_surjective α β hα)]
    exact h
  · exact Or.inl (mem_range_comap_pullbackFst_of_not_ker α β p h)

private theorem exists_ideal_lift_pow (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) (J : Ideal A) (b : B)
    (hb : ∀ q : PrimeSpectrum C,
      (∀ a ∈ J, α a ∈ q.asIdeal) → β b ∈ q.asIdeal) :
    ∃ (n : ℕ) (a : A), 0 < n ∧ a ∈ J ∧ α a = β (b ^ n) := by
  have hrad : β b ∈ (J.map α).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical, mem_vanishingIdeal]
    intro q hq
    apply hb q
    intro a ha
    exact hq (Ideal.mem_map_of_mem α ha)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective α hα).mp hn
  obtain ⟨t, ht⟩ := hα (β b)
  refine ⟨n + 1, a * t, Nat.zero_lt_succ n, J.mul_mem_right t ha, ?_⟩
  simp only [map_mul, map_pow, hae, ht, pow_succ]

private theorem comap_pullbackFst_injective_off (α : A →+* C) (β : B →+* C)
    (a₁ a₂ : PrimeSpectrum A)
    (ha : ¬ RingHom.ker α ≤ a₁.asIdeal)
    (heq : comap (α.pullbackFst β) a₁ = comap (α.pullbackFst β) a₂) :
    a₁ = a₂ := by
  obtain ⟨i, hi, hip⟩ := SetLike.not_le_iff_exists.mp ha
  have hip₂ : i ∉ a₂.asIdeal := by
    let d : α.pullback β := ⟨(i, 0), by simpa [RingHom.mem_ker] using hi⟩
    have hd : d ∉ (comap (α.pullbackFst β) a₁).asIdeal := hip
    rw [heq] at hd
    exact hd
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro x
  have hx : i * x ∈ a₁.asIdeal ↔ i * x ∈ a₂.asIdeal := by
    let d : α.pullback β := ⟨(i * x, 0), by
      change α (i * x) = β 0
      simp [map_mul, show α i = 0 from hi]⟩
    have hd := congrArg (fun q : PrimeSpectrum (α.pullback β) => d ∈ q.asIdeal) heq
    change (i * x ∈ a₁.asIdeal) = (i * x ∈ a₂.asIdeal) at hd
    exact ⟨fun h => hd ▸ h, fun h => hd.symm ▸ h⟩
  constructor
  · intro h
    have himul : i * x ∈ a₁.asIdeal := a₁.asIdeal.mul_mem_left i h
    exact (a₂.isPrime.mem_or_mem (hx.mp himul)).resolve_left hip₂
  · intro h
    have himul : i * x ∈ a₂.asIdeal := a₂.asIdeal.mul_mem_left i h
    exact (a₁.isPrime.mem_or_mem (hx.mpr himul)).resolve_left hip

private theorem comap_pullbackFst_eq_pullbackSnd (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) (a : PrimeSpectrum A) (b : PrimeSpectrum B)
    (heq : comap (α.pullbackFst β) a = comap (α.pullbackSnd β) b) :
    ∃ c : PrimeSpectrum C, comap α c = a ∧ comap β c = b := by
  have hker : RingHom.ker α ≤ a.asIdeal := by
    intro i hi
    let d : α.pullback β := ⟨(i, 0), by simpa [RingHom.mem_ker] using hi⟩
    have hd : d ∈ (comap (α.pullbackSnd β) b).asIdeal := b.asIdeal.zero_mem
    rw [← heq] at hd
    exact hd
  have hrange : a ∈ Set.range (comap α) := by
    rw [range_comap_of_surjective _ _ hα]
    exact hker
  obtain ⟨c, hc⟩ := hrange
  refine ⟨c, hc, ?_⟩
  apply comap_injective_of_surjective (α.pullbackSnd β)
    (RingHom.surjective_pullbackSnd_of_surjective α β hα)
  calc
    comap (α.pullbackSnd β) (comap β c) =
        comap (α.pullbackFst β) (comap α c) := by
          rw [← comap_comp_apply, ← comap_comp_apply, RingHom.pullback_comm_sq]
    _ = comap (α.pullbackSnd β) b := by rw [hc, heq]

private theorem isOpen_pullback_iff_core (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) (V : Set (PrimeSpectrum (α.pullback β))) :
    IsOpen V ↔
      IsOpen ((comap (α.pullbackFst β)) ⁻¹' V) ∧
      IsOpen ((comap (α.pullbackSnd β)) ⁻¹' V) := by
  constructor
  · intro hV
    exact ⟨hV.preimage (continuous_comap _), hV.preimage (continuous_comap _)⟩
  · rintro ⟨hA, hB⟩
    obtain ⟨JA, hJA⟩ := (isClosed_iff_zeroLocus_ideal
      (((comap (α.pullbackFst β)) ⁻¹' V)ᶜ)).mp hA.isClosed_compl
    obtain ⟨JB, hJB⟩ := (isClosed_iff_zeroLocus_ideal
      (((comap (α.pullbackSnd β)) ⁻¹' V)ᶜ)).mp hB.isClosed_compl
    let J : Ideal (α.pullback β) :=
      (JA.comap (α.pullbackFst β)) ⊓ (JB.comap (α.pullbackSnd β))
    have hAchar (a : PrimeSpectrum A) :
        comap (α.pullbackFst β) a ∈ V ↔ ¬ JA ≤ a.asIdeal := by
      have h := Set.ext_iff.mp hJA a
      simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroLocus] at h
      tauto
    have hBchar (b : PrimeSpectrum B) :
        comap (α.pullbackSnd β) b ∈ V ↔ ¬ JB ≤ b.asIdeal := by
      have h := Set.ext_iff.mp hJB b
      simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroLocus] at h
      tauto
    have hsquare (q : PrimeSpectrum C) :
        comap (α.pullbackFst β) (comap α q) =
          comap (α.pullbackSnd β) (comap β q) := by
      rw [← comap_comp_apply, ← comap_comp_apply, RingHom.pullback_comm_sq]
    have hcompat (q : PrimeSpectrum C) :
        JA ≤ (comap α q).asIdeal ↔ JB ≤ (comap β q).asIdeal := by
      have heq : comap (α.pullbackFst β) (comap α q) ∈ V ↔
          comap (α.pullbackSnd β) (comap β q) ∈ V := by rw [hsquare]
      have hleft := hAchar (comap α q)
      have hright := hBchar (comap β q)
      tauto
    have hlift (b : B) (hb : b ∈ JB) :
        ∃ (n : ℕ) (a : A), 0 < n ∧ a ∈ JA ∧ α a = β (b ^ n) := by
      apply exists_ideal_lift_pow α β hα JA b
      intro q hq
      have hJAq : JA ≤ (comap α q).asIdeal := by
        intro a ha
        exact hq a ha
      exact (hcompat q).mp hJAq hb
    have hBpre (b : PrimeSpectrum B) :
        comap (α.pullbackSnd β) b ∈ (zeroLocus J)ᶜ ↔
          comap (α.pullbackSnd β) b ∈ V := by
      rw [hBchar]
      simp only [Set.mem_compl_iff, mem_zeroLocus]
      change (¬ J ≤ (comap (α.pullbackSnd β) b).asIdeal) ↔ ¬ JB ≤ b.asIdeal
      constructor
      · intro hJ hB
        apply hJ
        intro d hd
        exact hB (show (α.pullbackSnd β) d ∈ JB from hd.2)
      · intro hB
        obtain ⟨element, helement, helementb⟩ := SetLike.not_le_iff_exists.mp hB
        obtain ⟨n, a, hn, ha, heq⟩ := hlift element helement
        let d : α.pullback β := ⟨(a, element ^ n), heq⟩
        apply SetLike.not_le_iff_exists.mpr
        refine ⟨d, ?_, ?_⟩
        · change d.1.1 ∈ JA ∧ d.1.2 ∈ JB
          exact ⟨ha, JB.pow_mem_of_mem helement n hn⟩
        · intro hpow
          change element ^ n ∈ b.asIdeal at hpow
          exact helementb (b.isPrime.mem_of_pow_mem n hpow)
    have hApre (a : PrimeSpectrum A) :
        comap (α.pullbackFst β) a ∈ (zeroLocus J)ᶜ ↔
          comap (α.pullbackFst β) a ∈ V := by
      rw [hAchar]
      simp only [Set.mem_compl_iff, mem_zeroLocus]
      change (¬ J ≤ (comap (α.pullbackFst β) a).asIdeal) ↔ ¬ JA ≤ a.asIdeal
      constructor
      · intro hJ hA
        apply hJ
        intro d hd
        exact hA (show (α.pullbackFst β) d ∈ JA from hd.1)
      · intro hA
        by_cases hker : RingHom.ker α ≤ a.asIdeal
        · have hrange : a ∈ Set.range (comap α) := by
            rw [range_comap_of_surjective _ _ hα]
            exact hker
          obtain ⟨q, rfl⟩ := hrange
          have hB : ¬ JB ≤ (comap β q).asIdeal :=
            fun h => hA ((hcompat q).mpr h)
          have hq := (hBpre (comap β q)).mpr ((hBchar (comap β q)).mpr hB)
          rwa [← hsquare] at hq
        · obtain ⟨i, hi, hin⟩ := SetLike.not_le_iff_exists.mp hker
          obtain ⟨element, helement, helementa⟩ := SetLike.not_le_iff_exists.mp hA
          let d : α.pullback β := ⟨(i * element, 0), by
            change α (i * element) = β 0
            simp [map_mul, show α i = 0 from hi]⟩
          apply SetLike.not_le_iff_exists.mpr
          refine ⟨d, ?_, ?_⟩
          · change d.1.1 ∈ JA ∧ d.1.2 ∈ JB
            exact ⟨JA.mul_mem_left i helement, JB.zero_mem⟩
          · intro hmul
            change i * element ∈ a.asIdeal at hmul
            exact helementa ((a.isPrime.mem_or_mem hmul).resolve_left hin)
    have hVe : V = (zeroLocus J)ᶜ := by
      ext p
      rcases range_comap_pullback_cover α β hα p with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact (hApre a).symm
      · exact (hBpre b).symm
    rw [hVe]
    exact (isClosed_zeroLocus _).isOpen_compl

private theorem existsUnique_continuousMap_pullback_core
    (α : A →+* C) (β : B →+* C) (hα : Function.Surjective α)
    {X : Type uX} [TopologicalSpace X]
    (fA : C(PrimeSpectrum A, X)) (fB : C(PrimeSpectrum B, X))
    (hagree : ∀ c, fA (comap α c) = fB (comap β c)) :
    ∃! fD : C(PrimeSpectrum (α.pullback β), X),
      (∀ a, fD (comap (α.pullbackFst β) a) = fA a) ∧
      (∀ b, fD (comap (α.pullbackSnd β) b) = fB b) := by
  classical
  have hπB : Function.Surjective (α.pullbackSnd β) :=
    RingHom.surjective_pullbackSnd_of_surjective α β hα
  have hπBinj : Function.Injective (comap (α.pullbackSnd β)) :=
    comap_injective_of_surjective _ hπB
  have hcover (p : PrimeSpectrum (α.pullback β)) :
      (∃ a, comap (α.pullbackFst β) a = p) ∨
        (∃ b, comap (α.pullbackSnd β) b = p) :=
    range_comap_pullback_cover α β hα p
  let descend (p : PrimeSpectrum (α.pullback β)) : X :=
    if h : ∃ b, comap (α.pullbackSnd β) b = p then fB (Classical.choose h)
    else fA (Classical.choose ((hcover p).resolve_right h))
  have hBface (b : PrimeSpectrum B) :
      descend (comap (α.pullbackSnd β) b) = fB b := by
    unfold descend
    split_ifs with h
    · congr 1
      exact hπBinj (Classical.choose_spec h)
    · exact (h ⟨b, rfl⟩).elim
  have hAface (a : PrimeSpectrum A) :
      descend (comap (α.pullbackFst β) a) = fA a := by
    unfold descend
    split_ifs with h
    · obtain ⟨c, hcA, hcB⟩ := comap_pullbackFst_eq_pullbackSnd α β hα a
        (Classical.choose h) (Classical.choose_spec h).symm
      calc
        fB (Classical.choose h) = fB (comap β c) := by rw [hcB]
        _ = fA (comap α c) := (hagree c).symm
        _ = fA a := by rw [hcA]
    · have ha : ¬ RingHom.ker α ≤ a.asIdeal := by
        intro hker
        have hrange : a ∈ Set.range (comap α) := by
          rw [range_comap_of_surjective _ _ hα]
          exact hker
        obtain ⟨c, hc⟩ := hrange
        apply h
        refine ⟨comap β c, ?_⟩
        rw [← hc, ← comap_comp_apply, ← comap_comp_apply,
          RingHom.pullback_comm_sq]
      have hchoose := Classical.choose_spec ((hcover _).resolve_right h)
      congr 1
      exact (comap_pullbackFst_injective_off α β a _ ha hchoose.symm).symm
  have hcont : Continuous descend := by
    apply continuous_def.2
    intro U hU
    apply (isOpen_pullback_iff_core α β hα (descend ⁻¹' U)).mpr
    constructor
    · have hpre : (comap (α.pullbackFst β)) ⁻¹' (descend ⁻¹' U) = fA ⁻¹' U := by
        ext a
        change descend (comap (α.pullbackFst β) a) ∈ U ↔ fA a ∈ U
        rw [hAface]
      rw [hpre]
      exact hU.preimage fA.continuous
    · have hpre : (comap (α.pullbackSnd β)) ⁻¹' (descend ⁻¹' U) = fB ⁻¹' U := by
        ext b
        change descend (comap (α.pullbackSnd β) b) ∈ U ↔ fB b ∈ U
        rw [hBface]
      rw [hpre]
      exact hU.preimage fB.continuous
  refine ⟨⟨descend, hcont⟩, ⟨hAface, hBface⟩, ?_⟩
  intro other hother
  apply ContinuousMap.ext
  intro p
  rcases hcover p with ⟨a, ha⟩ | ⟨b, hb⟩
  · rw [← ha, hother.1]
    exact (hAface a).symm
  · rw [← hb, hother.2]
    exact (hBface b).symm

/-- For a surjective `α`, the entire spectrum of the ring pullback is the
pushout in `TopCat`, including the closed gluing locus. Only `α` is assumed
surjective; all ring-carrier universes are independent. `IsPushout.desc`,
`IsPushout.inl_desc`, `IsPushout.inr_desc`, and `IsPushout.hom_ext` give its
universal property after lifting target spaces to this universe. -/
theorem isPushout_pullback (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) :
    IsPushout
      (comapULift.{uA, uC, max uA uB uC w} α)
      (comapULift.{uB, uC, max uA uB uC w} β)
      (comapULift.{max uA uB, uA, max uA uB uC w} (α.pullbackFst β))
      (comapULift.{max uA uB, uB, max uA uB uC w} (α.pullbackSnd β)) := by
  classical
  let f := comapULift.{uA, uC, max uA uB uC w} α
  let g := comapULift.{uB, uC, max uA uB uC w} β
  let inl := comapULift.{max uA uB, uA, max uA uB uC w} (α.pullbackFst β)
  let inr := comapULift.{max uA uB, uB, max uA uB uC w} (α.pullbackSnd β)
  have comm : f ≫ inl = g ≫ inr := comapULift_pullback_comm α β
  let fromA (s : PushoutCocone f g) : C(PrimeSpectrum A, s.pt) :=
    ⟨fun a => s.inl ⟨a⟩, s.inl.hom.continuous.comp
      (TopCat.uliftFunctorObjHomeo.{max uA uB uC w}
        (TopCat.of (PrimeSpectrum A))).continuous⟩
  let fromB (s : PushoutCocone f g) : C(PrimeSpectrum B, s.pt) :=
    ⟨fun b => s.inr ⟨b⟩, s.inr.hom.continuous.comp
      (TopCat.uliftFunctorObjHomeo.{max uA uB uC w}
        (TopCat.of (PrimeSpectrum B))).continuous⟩
  have agree (s : PushoutCocone f g) :
      ∀ c, fromA s (comap α c) = fromB s (comap β c) := by
    intro c
    have hc := congrArg (fun morphism => morphism ⟨c⟩) s.condition
    exact hc
  let extension (s : PushoutCocone f g) : C(PrimeSpectrum (α.pullback β), s.pt) :=
    Classical.choose (existsUnique_continuousMap_pullback_core α β hα
      (fromA s) (fromB s) (agree s))
  have extension_spec (s : PushoutCocone f g) :
      (∀ a, extension s (comap (α.pullbackFst β) a) = fromA s a) ∧
        (∀ b, extension s (comap (α.pullbackSnd β) b) = fromB s b) :=
    (Classical.choose_spec (existsUnique_continuousMap_pullback_core α β hα
      (fromA s) (fromB s) (agree s))).1
  let descend (s : PushoutCocone f g) :
      (TopCat.uliftFunctor.{max uA uB uC w}).obj
          (TopCat.of (PrimeSpectrum (α.pullback β))) ⟶ s.pt :=
    TopCat.ofHom ⟨fun p => extension s p.down, by fun_prop⟩
  have leftface (s : PushoutCocone f g) : inl ≫ descend s = s.inl := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    cases p with
    | up a => exact (extension_spec s).1 a
  have rightface (s : PushoutCocone f g) : inr ≫ descend s = s.inr := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    cases p with
    | up b => exact (extension_spec s).2 b
  change IsPushout f g inl inr
  refine { w := comm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk comm descend leftface rightface ?_
  intro s m hleft hright
  let other : C(PrimeSpectrum (α.pullback β), s.pt) :=
    ⟨fun p => m ⟨p⟩, m.hom.continuous.comp
      (TopCat.uliftFunctorObjHomeo.{max uA uB uC w}
        (TopCat.of (PrimeSpectrum (α.pullback β)))).continuous⟩
  have other_left : ∀ a, other (comap (α.pullbackFst β) a) = fromA s a := by
    intro a
    have ha := congrArg (fun morphism => morphism ⟨a⟩) hleft
    exact ha
  have other_right : ∀ b, other (comap (α.pullbackSnd β) b) = fromB s b := by
    intro b
    have hb := congrArg (fun morphism => morphism ⟨b⟩) hright
    exact hb
  have hother : other = extension s :=
    (Classical.choose_spec (existsUnique_continuousMap_pullback_core α β hα
      (fromA s) (fromB s) (agree s))).2 other ⟨other_left, other_right⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  cases p with
  | up point => exact congrArg (fun map : C(PrimeSpectrum (α.pullback β), s.pt) => map point) hother

/-- A set of primes in a surjective ring pullback is open exactly when its
preimages in both component spectra are open. In particular this describes
the quotient topology on the entire pullback spectrum. -/
theorem isOpen_pullback_iff (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) (V : Set (PrimeSpectrum (α.pullback β))) :
    IsOpen V ↔
      IsOpen ((comap (α.pullbackFst β)) ⁻¹' V) ∧
      IsOpen ((comap (α.pullbackSnd β)) ⁻¹' V) := by
  exact isOpen_pullback_iff_core α β hα V

/-- Compatible continuous maps out of both component spectra extend uniquely
over the spectrum of the ring pullback, with no restriction on the universe
of the target topological space. -/
theorem existsUnique_continuousMap_pullback (α : A →+* C) (β : B →+* C)
    (hα : Function.Surjective α) {X : Type uX} [TopologicalSpace X]
    (fA : C(PrimeSpectrum A, X)) (fB : C(PrimeSpectrum B, X))
    (hagree : ∀ c, fA (comap α c) = fB (comap β c)) :
    ∃! fD : C(PrimeSpectrum (α.pullback β), X),
      (∀ a, fD (comap (α.pullbackFst β) a) = fA a) ∧
      (∀ b, fD (comap (α.pullbackSnd β) b) = fB b) := by
  exact existsUnique_continuousMap_pullback_core α β hα fA fB hagree

end PrimeSpectrum
