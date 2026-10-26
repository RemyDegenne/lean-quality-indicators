/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Open immersions from a ring pullback

For arbitrary maps `f : R →+* T` and `g : S →+* T`, the projections from their
pullback become open immersions on the complements of `ker f` and `ker g`.
Their images are the complements of the *opposite* projection kernels, and
partition the complement of the kernel of the common map to `T`.

There are no surjectivity, nontriviality, or finiteness assumptions.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The common map from a fiber product of rings to its base. -/
def toBase (f : R →+* T) (g : S →+* T) : f.pullback g →+* T :=
  f.comp (f.pullbackFst g)

@[simp] theorem toBase_apply (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    toBase f g x = f x.1.1 := rfl

/-- The component kernels in a ring pullback annihilate one another. -/
theorem ker_fst_mul_ker_snd (f : R →+* T) (g : S →+* T) :
    RingHom.ker (f.pullbackFst g) * RingHom.ker (f.pullbackSnd g) = ⊥ := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker] at ha hb
    have hab : a * b = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change a.1.1 * b.1.1 = 0
        change a.1.1 = 0 at ha
        simp [ha]
      · change a.1.2 * b.1.2 = 0
        change b.1.2 = 0 at hb
        simp [hb]
    simpa using hab
  · exact bot_le

/-- The kernel of the common map is the sum of the component kernels. -/
theorem ker_toBase (f : R →+* T) (g : S →+* T) :
    RingHom.ker (toBase f g) =
      RingHom.ker (f.pullbackFst g) ⊔ RingHom.ker (f.pullbackSnd g) := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    have hfirst : f a.1.1 = 0 := ha
    have hsecond : g a.1.2 = 0 := a.2.symm.trans hfirst
    let ar : f.pullback g := ⟨(a.1.1, 0), by simp [hfirst]⟩
    let as : f.pullback g := ⟨(0, a.1.2), by simp [hsecond]⟩
    have har : ar ∈ RingHom.ker (f.pullbackSnd g) := by
      rw [RingHom.mem_ker]
      rfl
    have has : as ∈ RingHom.ker (f.pullbackFst g) := by
      rw [RingHom.mem_ker]
      rfl
    have hsum : as + ar = a := by
      apply Subtype.ext
      apply Prod.ext <;> simp [ar, as]
    rw [← hsum]
    exact Ideal.add_mem _ (Ideal.mem_sup_left has) (Ideal.mem_sup_right har)
  · rw [sup_le_iff]
    constructor
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      change f a.1.1 = 0
      change a.1.1 = 0 at ha
      simp [ha]
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      change f a.1.1 = 0
      change a.1.2 = 0 at ha
      calc
        f a.1.1 = g a.1.2 := a.2
        _ = g 0 := congrArg g ha
        _ = 0 := map_zero g

/-- A projection of a ring pullback is an isomorphism after localizing at an
element of the kernel of the opposite projection. -/
theorem awayMap_fst_bijective (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackSnd g)) :
    Function.Bijective (Localization.awayMap (f.pullbackFst g) b) := by
  have hb0 : b.1.2 = 0 := by
    have h := (RingHom.mem_ker).mp hb
    exact h
  have hbf : f b.1.1 = 0 := by
    calc
      f b.1.1 = g b.1.2 := b.2
      _ = 0 := by simp [hb0]
  constructor
  · apply (Localization.awayMap_injective_iff).2
    intro a ha
    refine ⟨1, ?_⟩
    have hmul : b * a = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change b.1.1 * a.1.1 = 0
        change a.1.1 = 0 at ha
        simp [ha]
      · change b.1.2 * a.1.2 = 0
        simp [hb0]
    simpa only [pow_one] using hmul
  · apply (Localization.awayMap_surjective_iff).2
    intro a
    let c : f.pullback g := ⟨(b.1.1 * a, 0), by simp [map_mul, hbf]⟩
    refine ⟨c, 1, ?_⟩
    change b.1.1 * a = b.1.1 ^ 1 * a
    rw [pow_one]

/-- The symmetric localized projection is likewise bijective. -/
theorem awayMap_snd_bijective (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackFst g)) :
    Function.Bijective (Localization.awayMap (f.pullbackSnd g) b) := by
  have hb0 : b.1.1 = 0 := by
    have h := (RingHom.mem_ker).mp hb
    exact h
  have hbg : g b.1.2 = 0 := by
    calc
      g b.1.2 = f b.1.1 := b.2.symm
      _ = 0 := by simp [hb0]
  constructor
  · apply (Localization.awayMap_injective_iff).2
    intro a ha
    refine ⟨1, ?_⟩
    have hmul : b * a = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change b.1.1 * a.1.1 = 0
        simp [hb0]
      · change b.1.2 * a.1.2 = 0
        change a.1.2 = 0 at ha
        simp [ha]
    simpa only [pow_one] using hmul
  · apply (Localization.awayMap_surjective_iff).2
    intro a
    let c : f.pullback g := ⟨(0, b.1.2 * a), by simp [map_mul, hbg]⟩
    refine ⟨c, 1, ?_⟩
    change b.1.2 * a = b.1.2 ^ 1 * a
    rw [pow_one]

/-- The open complement of a ring map's kernel in its domain spectrum. -/
def kernelComplement {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (RingHom.ker q : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The restricted source of the first projection. -/
def fstSource (f : R →+* T) (_g : S →+* T) : (Spec (.of R)).Opens :=
  kernelComplement f

/-- The restricted source of the second projection. -/
def sndSource (_f : R →+* T) (g : S →+* T) : (Spec (.of S)).Opens :=
  kernelComplement g

/-- The first projection on spectra. -/
def fstMap (f : R →+* T) (g : S →+* T) :
    Spec (.of R) ⟶ Spec (.of (f.pullback g)) :=
  Spec.map (CommRingCat.ofHom (f.pullbackFst g))

/-- The second projection on spectra. -/
def sndMap (f : R →+* T) (g : S →+* T) :
    Spec (.of S) ⟶ Spec (.of (f.pullback g)) :=
  Spec.map (CommRingCat.ofHom (f.pullbackSnd g))

/-- The first projection, restricted to the complement of `ker f`. -/
def fstOpenMap (f : R →+* T) (g : S →+* T) :
    (fstSource f g : Scheme) ⟶ Spec (.of (f.pullback g)) :=
  (fstSource f g).ι ≫ fstMap f g

/-- The second projection, restricted to the complement of `ker g`. -/
def sndOpenMap (f : R →+* T) (g : S →+* T) :
    (sndSource f g : Scheme) ⟶ Spec (.of (f.pullback g)) :=
  (sndSource f g).ι ≫ sndMap f g

/-- The image of the first restricted map is the complement of the *second*
projection kernel. -/
def fstTarget (f : R →+* T) (g : S →+* T) :
    (Spec (.of (f.pullback g))).Opens :=
  kernelComplement (f.pullbackSnd g)

/-- The image of the second restricted map is the complement of the *first*
projection kernel. -/
def sndTarget (f : R →+* T) (g : S →+* T) :
    (Spec (.of (f.pullback g))).Opens :=
  kernelComplement (f.pullbackFst g)

/-- The open complement of the common-target kernel. -/
def commonTarget (f : R →+* T) (g : S →+* T) :
    (Spec (.of (f.pullback g))).Opens :=
  kernelComplement (toBase f g)

theorem fstTarget_inf_sndTarget (f : R →+* T) (g : S →+* T) :
    fstTarget f g ⊓ sndTarget f g = ⊥ := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackSnd g)) : Set (f.pullback g)))ᶜ ∩
      (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackFst g)) : Set (f.pullback g)))ᶜ = ∅
  rw [← Set.compl_union, Set.union_comm, ← PrimeSpectrum.zeroLocus_mul,
    ker_fst_mul_ker_snd, PrimeSpectrum.zeroLocus_bot]
  simp

theorem fstTarget_sup_sndTarget (f : R →+* T) (g : S →+* T) :
    fstTarget f g ⊔ sndTarget f g = commonTarget f g := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackSnd g)) : Set (f.pullback g)))ᶜ ∪
      (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackFst g)) : Set (f.pullback g)))ᶜ =
      (PrimeSpectrum.zeroLocus (↑(RingHom.ker (toBase f g)) : Set (f.pullback g)))ᶜ
  rw [← Set.compl_inter, Set.inter_comm, ← PrimeSpectrum.zeroLocus_sup,
    ← ker_toBase]

private theorem fst_chart_iso (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackSnd g)) :
    IsIso (fstMap f g ∣_ PrimeSpectrum.basicOpen b) := by
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (f.pullbackFst g) b)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (awayMap_fst_bijective f g b hb)
  change IsIso (Spec.map (CommRingCat.ofHom (f.pullbackFst g)) ∣_
    PrimeSpectrum.basicOpen b)
  exact (Arrow.isIso_iff_isIso_of_isIso
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (f.pullbackFst g)) b).hom).mpr inferInstance

private theorem snd_chart_iso (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackFst g)) :
    IsIso (sndMap f g ∣_ PrimeSpectrum.basicOpen b) := by
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (f.pullbackSnd g) b)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (awayMap_snd_bijective f g b hb)
  change IsIso (Spec.map (CommRingCat.ofHom (f.pullbackSnd g)) ∣_
    PrimeSpectrum.basicOpen b)
  exact (Arrow.isIso_iff_isIso_of_isIso
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (f.pullbackSnd g)) b).hom).mpr inferInstance

private theorem fst_chart_le (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackSnd g)) :
    fstMap f g ⁻¹ᵁ PrimeSpectrum.basicOpen b ≤ fstSource f g := by
  intro x hx
  have hb0 : b.1.2 = 0 := (RingHom.mem_ker).mp hb
  have hbf : f b.1.1 = 0 := by
    calc
      f b.1.1 = g b.1.2 := b.2
      _ = 0 := by simp [hb0]
  have hbx : (f.pullbackFst g) b ∉ x.asIdeal := by
    change b ∉ (PrimeSpectrum.comap (f.pullbackFst g) x).asIdeal
    exact (PrimeSpectrum.mem_basicOpen b _).mp hx
  change ¬ (RingHom.ker f : Set R) ⊆ x.asIdeal
  intro h
  exact hbx (h hbf)

private theorem snd_chart_le (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackFst g)) :
    sndMap f g ⁻¹ᵁ PrimeSpectrum.basicOpen b ≤ sndSource f g := by
  intro x hx
  have hb0 : b.1.1 = 0 := (RingHom.mem_ker).mp hb
  have hbg : g b.1.2 = 0 := by
    calc
      g b.1.2 = f b.1.1 := b.2.symm
      _ = 0 := by simp [hb0]
  have hbx : (f.pullbackSnd g) b ∉ x.asIdeal := by
    change b ∉ (PrimeSpectrum.comap (f.pullbackSnd g) x).asIdeal
    exact (PrimeSpectrum.mem_basicOpen b _).mp hx
  change ¬ (RingHom.ker g : Set S) ⊆ x.asIdeal
  intro h
  exact hbx (h hbg)

/-- The first restricted scheme morphism is an open immersion without any
surjectivity assumption on the ring maps. -/
theorem isOpenImmersion_fstOpenMap (f : R →+* T) (g : S →+* T) :
    IsOpenImmersion (fstOpenMap f g) := by
  apply IsOpenImmersion.of_forall_source_exists (fstOpenMap f g)
  · intro x y hxy
    change fstMap f g x.1 = fstMap f g y.1 at hxy
    have hx : ¬ (RingHom.ker f : Set R) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(a, 0), by simpa [RingHom.mem_ker] using ha⟩
    have hb : b ∈ RingHom.ker (f.pullbackSnd g) := by
      rw [RingHom.mem_ker]
      rfl
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    have hxV : x.1 ∈ fstMap f g ⁻¹ᵁ V := by
      change b ∉ (PrimeSpectrum.comap (f.pullbackFst g) x.1).asIdeal
      exact hax
    have hyV : y.1 ∈ fstMap f g ⁻¹ᵁ V := by
      change fstMap f g y.1 ∈ V
      rw [← hxy]
      exact hxV
    have : IsIso (fstMap f g ∣_ V) := fst_chart_iso f g b hb
    have hrestr : (fstMap f g ∣_ V) ⟨x.1, hxV⟩ =
        (fstMap f g ∣_ V) ⟨y.1, hyV⟩ := by
      apply Subtype.ext
      calc
        ((fstMap f g ∣_ V) ⟨x.1, hxV⟩).1 = fstMap f g x.1 :=
          morphismRestrict_base_coe (fstMap f g) V ⟨x.1, hxV⟩
        _ = fstMap f g y.1 := hxy
        _ = ((fstMap f g ∣_ V) ⟨y.1, hyV⟩).1 :=
          (morphismRestrict_base_coe (fstMap f g) V ⟨y.1, hyV⟩).symm
    have h := (fstMap f g ∣_ V).isOpenEmbedding.injective hrestr
    have hbase : x.1 = y.1 := congrArg (fun z => z.1) h
    exact Subtype.ext hbase
  · intro x
    have hx : ¬ (RingHom.ker f : Set R) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(a, 0), by simpa [RingHom.mem_ker] using ha⟩
    have hb : b ∈ RingHom.ker (f.pullbackSnd g) := by
      rw [RingHom.mem_ker]
      rfl
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    let W := fstMap f g ⁻¹ᵁ V
    let i : (W : Scheme) ⟶ (fstSource f g : Scheme) :=
      (Spec (.of R)).homOfLE (fst_chart_le f g b hb)
    have hi : IsOpenImmersion i := inferInstance
    refine ⟨W, i, hi, ?_, ?_⟩
    · change ∃ z, i z = x
      refine ⟨⟨x.1, ?_⟩, ?_⟩
      · change b ∉ (PrimeSpectrum.comap (f.pullbackFst g) x.1).asIdeal
        exact hax
      · simp only [i, Scheme.homOfLE_apply']
        exact Subtype.ext rfl
    · have : IsIso (fstMap f g ∣_ V) := fst_chart_iso f g b hb
      change IsOpenImmersion (i ≫ (fstSource f g).ι ≫ fstMap f g)
      rw [← Category.assoc, Scheme.homOfLE_ι]
      have hcomp : W.ι ≫ fstMap f g = (fstMap f g ∣_ V) ≫ V.ι :=
        (morphismRestrict_ι (fstMap f g) V).symm
      rw [hcomp]
      infer_instance

/-- The symmetric restricted scheme morphism is an open immersion. -/
theorem isOpenImmersion_sndOpenMap (f : R →+* T) (g : S →+* T) :
    IsOpenImmersion (sndOpenMap f g) := by
  apply IsOpenImmersion.of_forall_source_exists (sndOpenMap f g)
  · intro x y hxy
    change sndMap f g x.1 = sndMap f g y.1 at hxy
    have hx : ¬ (RingHom.ker g : Set S) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(0, a), by simpa [RingHom.mem_ker] using ha.symm⟩
    have hb : b ∈ RingHom.ker (f.pullbackFst g) := by
      rw [RingHom.mem_ker]
      rfl
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    have hxV : x.1 ∈ sndMap f g ⁻¹ᵁ V := by
      change b ∉ (PrimeSpectrum.comap (f.pullbackSnd g) x.1).asIdeal
      exact hax
    have hyV : y.1 ∈ sndMap f g ⁻¹ᵁ V := by
      change sndMap f g y.1 ∈ V
      rw [← hxy]
      exact hxV
    have : IsIso (sndMap f g ∣_ V) := snd_chart_iso f g b hb
    have hrestr : (sndMap f g ∣_ V) ⟨x.1, hxV⟩ =
        (sndMap f g ∣_ V) ⟨y.1, hyV⟩ := by
      apply Subtype.ext
      calc
        ((sndMap f g ∣_ V) ⟨x.1, hxV⟩).1 = sndMap f g x.1 :=
          morphismRestrict_base_coe (sndMap f g) V ⟨x.1, hxV⟩
        _ = sndMap f g y.1 := hxy
        _ = ((sndMap f g ∣_ V) ⟨y.1, hyV⟩).1 :=
          (morphismRestrict_base_coe (sndMap f g) V ⟨y.1, hyV⟩).symm
    have h := (sndMap f g ∣_ V).isOpenEmbedding.injective hrestr
    have hbase : x.1 = y.1 := congrArg (fun z => z.1) h
    exact Subtype.ext hbase
  · intro x
    have hx : ¬ (RingHom.ker g : Set S) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(0, a), by simpa [RingHom.mem_ker] using ha.symm⟩
    have hb : b ∈ RingHom.ker (f.pullbackFst g) := by
      rw [RingHom.mem_ker]
      rfl
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    let W := sndMap f g ⁻¹ᵁ V
    let i : (W : Scheme) ⟶ (sndSource f g : Scheme) :=
      (Spec (.of S)).homOfLE (snd_chart_le f g b hb)
    have hi : IsOpenImmersion i := inferInstance
    refine ⟨W, i, hi, ?_, ?_⟩
    · change ∃ z, i z = x
      refine ⟨⟨x.1, ?_⟩, ?_⟩
      · change b ∉ (PrimeSpectrum.comap (f.pullbackSnd g) x.1).asIdeal
        exact hax
      · simp only [i, Scheme.homOfLE_apply']
        exact Subtype.ext rfl
    · have : IsIso (sndMap f g ∣_ V) := snd_chart_iso f g b hb
      change IsOpenImmersion (i ≫ (sndSource f g).ι ≫ sndMap f g)
      rw [← Category.assoc, Scheme.homOfLE_ι]
      have hcomp : W.ι ≫ sndMap f g = (sndMap f g ∣_ V) ≫ V.ι :=
        (morphismRestrict_ι (sndMap f g) V).symm
      rw [hcomp]
      infer_instance

instance (f : R →+* T) (g : S →+* T) : IsOpenImmersion (fstOpenMap f g) :=
  isOpenImmersion_fstOpenMap f g

instance (f : R →+* T) (g : S →+* T) : IsOpenImmersion (sndOpenMap f g) :=
  isOpenImmersion_sndOpenMap f g

/-- The exact open image of the first restricted scheme morphism. -/
theorem range_fstOpenMap (f : R →+* T) (g : S →+* T) :
    Set.range (fstOpenMap f g) = (fstTarget f g : Set (Spec (.of (f.pullback g)))) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    have hx : ¬ (RingHom.ker f : Set R) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(a, 0), by simpa [RingHom.mem_ker] using ha⟩
    have hb : b ∈ RingHom.ker (f.pullbackSnd g) := by
      rw [RingHom.mem_ker]
      rfl
    change ¬ (↑(RingHom.ker (f.pullbackSnd g)) : Set (f.pullback g)) ⊆
      (↑((fstOpenMap f g x).asIdeal) : Set (f.pullback g))
    intro h
    exact hax (h hb)
  · intro hp
    have hp' : ¬ (↑(RingHom.ker (f.pullbackSnd g)) : Set (f.pullback g)) ⊆
        (↑p.asIdeal : Set (f.pullback g)) := hp
    obtain ⟨b, hb, hbp⟩ := Set.not_subset.mp hp'
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    have hpV : p ∈ V := (PrimeSpectrum.mem_basicOpen b p).mpr hbp
    have : IsIso (fstMap f g ∣_ V) := fst_chart_iso f g b hb
    let z : fstMap f g ⁻¹ᵁ V := inv (fstMap f g ∣_ V) ⟨p, hpV⟩
    have hz : fstMap f g z.1 = p := by
      have h : (fstMap f g ∣_ V) z = (⟨p, hpV⟩ : V) := by
        simpa only [z, asIso_inv, asIso_hom] using
          Scheme.inv_hom_apply (asIso (fstMap f g ∣_ V)) ⟨p, hpV⟩
      calc
        fstMap f g z.1 = ((fstMap f g ∣_ V) z).1 :=
          (morphismRestrict_base_coe (fstMap f g) V z).symm
        _ = p := congrArg Subtype.val h
    exact ⟨⟨z.1, fst_chart_le f g b hb z.2⟩, hz⟩

/-- The exact open image of the second restricted scheme morphism. -/
theorem range_sndOpenMap (f : R →+* T) (g : S →+* T) :
    Set.range (sndOpenMap f g) = (sndTarget f g : Set (Spec (.of (f.pullback g)))) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    have hx : ¬ (RingHom.ker g : Set S) ⊆ x.1.asIdeal := x.2
    obtain ⟨a, ha, hax⟩ := Set.not_subset.mp hx
    let b : f.pullback g := ⟨(0, a), by simpa [RingHom.mem_ker] using ha.symm⟩
    have hb : b ∈ RingHom.ker (f.pullbackFst g) := by
      rw [RingHom.mem_ker]
      rfl
    change ¬ (↑(RingHom.ker (f.pullbackFst g)) : Set (f.pullback g)) ⊆
      (↑((sndOpenMap f g x).asIdeal) : Set (f.pullback g))
    intro h
    exact hax (h hb)
  · intro hp
    have hp' : ¬ (↑(RingHom.ker (f.pullbackFst g)) : Set (f.pullback g)) ⊆
        (↑p.asIdeal : Set (f.pullback g)) := hp
    obtain ⟨b, hb, hbp⟩ := Set.not_subset.mp hp'
    let V : (Spec (.of (f.pullback g))).Opens := PrimeSpectrum.basicOpen b
    have hpV : p ∈ V := (PrimeSpectrum.mem_basicOpen b p).mpr hbp
    have : IsIso (sndMap f g ∣_ V) := snd_chart_iso f g b hb
    let z : sndMap f g ⁻¹ᵁ V := inv (sndMap f g ∣_ V) ⟨p, hpV⟩
    have hz : sndMap f g z.1 = p := by
      have h : (sndMap f g ∣_ V) z = (⟨p, hpV⟩ : V) := by
        simpa only [z, asIso_inv, asIso_hom] using
          Scheme.inv_hom_apply (asIso (sndMap f g ∣_ V)) ⟨p, hpV⟩
      calc
        sndMap f g z.1 = ((sndMap f g ∣_ V) z).1 :=
          (morphismRestrict_base_coe (sndMap f g) V z).symm
        _ = p := congrArg Subtype.val h
    exact ⟨⟨z.1, snd_chart_le f g b hb z.2⟩, hz⟩

/-- The images of the two restricted scheme morphisms are disjoint. -/
theorem disjoint_ranges (f : R →+* T) (g : S →+* T) :
    Disjoint (Set.range (fstOpenMap f g)) (Set.range (sndOpenMap f g)) := by
  rw [range_fstOpenMap, range_sndOpenMap]
  apply Set.disjoint_iff_inter_eq_empty.mpr
  change (fstTarget f g).1 ∩ (sndTarget f g).1 = ∅
  exact congrArg (fun U : (Spec (.of (f.pullback g))).Opens => U.1)
    (fstTarget_inf_sndTarget f g)

/-- The two exact ranges jointly cover the common-target-kernel complement. -/
theorem union_ranges (f : R →+* T) (g : S →+* T) :
    Set.range (fstOpenMap f g) ∪ Set.range (sndOpenMap f g) =
      (commonTarget f g : Set (Spec (.of (f.pullback g)))) := by
  rw [range_fstOpenMap, range_sndOpenMap]
  change (fstTarget f g).1 ∪ (sndTarget f g).1 = (commonTarget f g).1
  exact congrArg (fun U : (Spec (.of (f.pullback g))).Opens => U.1)
    (fstTarget_sup_sndTarget f g)

end AlgebraicGeometry.PullbackOpenImmersion
