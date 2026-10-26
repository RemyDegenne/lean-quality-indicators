/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IdealCompletion
public import Mathlib.Order.PrimeIdeal
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.Order.Category.FrameAdjunction
public import Mathlib.Topology.Spectral.Basic

/-!
# Prime-ideal spectra of bounded distributive lattices

`PrimeIdealSpectrum A` is identified with the point space of the frame of order
ideals of `A`. Its opens are the sets `D(I)` of prime ideals not containing `I`;
`idealOpenOrderIso` identifies order ideals with opens. The compact such opens
are exactly those from principal ideals. These give a compact-open basis and,
together with prime separation and generic points, a spectral-space structure.

Specialization is prime-ideal inclusion, or equivalently reverse inclusion of
the complementary prime filters. No nontriviality assumption on `A` is required.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), Definitions 2.2.6–2.2.7 and Theorem 2.2.8(1).
- Mathlib, `Order.PrimeIdeal`, `Order.PrimeSeparator` and `Topology.Spectral.Basic`;
  Formal Frontier Agents, *Ideal Completion*, for the order-ideal frame and
  compact-principal identification used here.
-/

public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

/-- The prime-ideal spectrum of a bounded distributive lattice, in the sense of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, §2.2(b), Definition 2.2.7. -/
abbrev PrimeIdealSpectrum (A : Type u) [DistribLattice A] [BoundedOrder A] :=
  {P : Order.Ideal A // P.IsPrime}

namespace PrimeIdealSpectrum

omit [BoundedOrder A] in
private theorem exists_mem_not_mem_of_not_le {I P : Order.Ideal A} (h : ¬ I ≤ P) :
    ∃ a ∈ I, a ∉ P := by
  exact Set.not_subset.mp h

/-- The prime filter complementary to a prime ideal. -/
def primeFilter (P : PrimeIdealSpectrum A) : Order.PFilter A :=
  P.2.compl_filter.toPFilter

@[simp] theorem mem_primeFilter (P : PrimeIdealSpectrum A) (a : A) :
    a ∈ primeFilter P ↔ a ∉ P.1 :=
  Iff.rfl

theorem primeFilter_isPrime (P : PrimeIdealSpectrum A) :
    (primeFilter P).IsPrime :=
  P.2.toPrimePair.F_isPrime

/-- A prime ideal determines a point of the frame of order ideals. -/
def toPoint (P : PrimeIdealSpectrum A) : Locale.PT (Order.Ideal A) where
  toFun I := ¬ I ≤ P.1
  map_inf' I J := by
    apply propext
    constructor
    · intro h
      exact ⟨fun hIP => h (inf_le_left.trans hIP),
        fun hJP => h (inf_le_right.trans hJP)⟩
    · rintro ⟨hIP, hJP⟩ hIJ
      obtain ⟨a, haI, haP⟩ := exists_mem_not_mem_of_not_le hIP
      obtain ⟨b, hbJ, hbP⟩ := exists_mem_not_mem_of_not_le hJP
      have habP : a ⊓ b ∈ P.1 := hIJ ⟨I.lower inf_le_left haI, J.lower inf_le_right hbJ⟩
      exact (P.2.mem_or_mem habP).elim haP hbP
  map_top' := by
    apply propext
    constructor
    · intro _
      trivial
    · intro _ h
      exact P.2.top_notMem (h (show (⊤ : A) ∈ (⊤ : Order.Ideal A) by trivial))
  map_sSup' S := by
    apply propext
    rw [sSup_Prop_eq]
    simp only [Set.mem_image]
    constructor
    · intro h
      have hex : ∃ I ∈ S, ¬ I ≤ P.1 := by
        by_contra hn
        push Not at hn
        exact h (sSup_le hn)
      obtain ⟨I, hIS, hIP⟩ := hex
      exact ⟨¬ I ≤ P.1, ⟨I, hIS, rfl⟩, hIP⟩
    · rintro ⟨p, ⟨I, hIS, hEq⟩, hp⟩ hSP
      subst p
      exact hp ((le_sSup hIS).trans hSP)

private def ofPointIdeal (f : Locale.PT (Order.Ideal A)) : Order.Ideal A where
  carrier := {a | ¬ f (Order.Ideal.principal a)}
  nonempty' := by
    refine ⟨⊥, ?_⟩
    simp
  directed' := by
    rintro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    change ¬ f (Order.Ideal.principal (a ⊔ b))
    rw [show Order.Ideal.principal (a ⊔ b) =
      Order.Ideal.principal a ⊔ Order.Ideal.principal b from
        map_sup Order.Ideal.principalHom a b, map_sup f]
    exact fun h ↦ h.elim ha hb
  lower' := by
    intro a b hab ha hb
    exact ha (OrderHomClass.monotone f
      (Order.Ideal.principal_le_iff.mpr (Order.Ideal.mem_principal.mpr hab)) hb)

private theorem ofPointIdeal_isPrime (f : Locale.PT (Order.Ideal A)) :
    (ofPointIdeal f).IsPrime := by
  let _ : (ofPointIdeal f).IsProper := Order.Ideal.isProper_of_notMem (by
    change ¬ (¬ f (Order.Ideal.principal ⊤))
    rw [Order.Ideal.principal_top, map_top]
    simp)
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro a b hab
  change ¬ f (Order.Ideal.principal (a ⊓ b)) at hab
  rw [show Order.Ideal.principal (a ⊓ b) =
    Order.Ideal.principal a ⊓ Order.Ideal.principal b from
      map_inf Order.Ideal.principalHom a b, map_inf f] at hab
  exact Classical.not_and_iff_not_or_not.mp hab

/-- A point of the frame of order ideals determines a prime ideal. -/
def ofPoint (f : Locale.PT (Order.Ideal A)) : PrimeIdealSpectrum A :=
  ⟨ofPointIdeal f, ofPointIdeal_isPrime f⟩

theorem ofPoint_toPoint (P : PrimeIdealSpectrum A) : ofPoint (toPoint P) = P := by
  apply Subtype.ext
  apply Order.Ideal.ext
  ext a
  change ¬ (¬ Order.Ideal.principal a ≤ P.1) ↔ a ∈ P.1
  rw [not_not, Order.Ideal.principal_le_iff]

private theorem ideal_eq_sSup_principal (I : Order.Ideal A) :
    I = sSup (Order.Ideal.principal '' (I : Set A)) := by
  apply le_antisymm
  · intro a ha
    exact Order.Ideal.mem_of_mem_of_le Order.Ideal.mem_principal_self
      (le_sSup ⟨a, ha, rfl⟩)
  · apply sSup_le
    rintro _ ⟨a, ha, rfl⟩
    exact Order.Ideal.principal_le_iff.mpr ha

theorem toPoint_ofPoint (f : Locale.PT (Order.Ideal A)) : toPoint (ofPoint f) = f := by
  ext I
  change (¬ I ≤ ofPointIdeal f) ↔ f I
  constructor
  · intro h
    obtain ⟨a, haI, ha⟩ := exists_mem_not_mem_of_not_le h
    change ¬ (¬ f (Order.Ideal.principal a)) at ha
    exact OrderHomClass.monotone f (Order.Ideal.principal_le_iff.mpr haI)
      (Classical.not_not.mp ha)
  · intro hf hle
    rw [ideal_eq_sSup_principal I, map_sSup f] at hf
    rw [sSup_Prop_eq] at hf
    obtain ⟨_, ⟨_, ⟨a, haI, rfl⟩, rfl⟩, hfa⟩ := hf
    exact hle haI hfa

/-- Prime ideals are equivalent to points of the ideal frame. -/
def pointEquiv : PrimeIdealSpectrum A ≃ Locale.PT (Order.Ideal A) where
  toFun := toPoint
  invFun := ofPoint
  left_inv := ofPoint_toPoint
  right_inv := toPoint_ofPoint

/-- The basic open `D(I)` consists of the prime ideals which do not contain `I`. -/
@[expose]
def basicOpen (I : Order.Ideal A) : Set (PrimeIdealSpectrum A) :=
  {P | ¬ I ≤ P.1}

/-- The prime-spectrum topology transported from the point space of the ideal frame. -/
instance instTopologicalSpace : TopologicalSpace (PrimeIdealSpectrum A) :=
  TopologicalSpace.induced toPoint inferInstance

/-- Prime ideals with their Zariski topology are the points of the ideal frame. -/
def pointHomeomorph : PrimeIdealSpectrum A ≃ₜ Locale.PT (Order.Ideal A) :=
  pointEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

theorem isOpen_basicOpen (I : Order.Ideal A) : IsOpen (basicOpen I) := by
  change IsOpen (toPoint ⁻¹' {f : Locale.PT (Order.Ideal A) | f I})
  apply isOpen_induced
  exact ⟨I, rfl⟩

/-- Every open of the prime spectrum has the form `D(I)` for an order ideal `I`. -/
theorem isOpen_iff_exists_basicOpen (s : Set (PrimeIdealSpectrum A)) :
    IsOpen s ↔ ∃ I : Order.Ideal A, basicOpen I = s := by
  change @IsOpen _ ((inferInstance : TopologicalSpace (Locale.PT (Order.Ideal A))).induced
    toPoint) s ↔ _
  rw [isOpen_induced_iff]
  constructor
  · rintro ⟨t, ⟨I, hIt⟩, rfl⟩
    refine ⟨I, ?_⟩
    rw [← hIt]
    rfl
  · rintro ⟨I, rfl⟩
    exact ⟨{f : Locale.PT (Order.Ideal A) | f I}, ⟨I, rfl⟩, rfl⟩

/-- Specialization of prime ideals is inclusion in the same orientation. -/
theorem specializes_iff_ideal_le (P Q : PrimeIdealSpectrum A) :
    P ⤳ Q ↔ P.1 ≤ Q.1 := by
  constructor
  · intro hPQ a haP
    by_contra haQ
    have hQopen : Q ∈ basicOpen (Order.Ideal.principal a) := by
      simpa only [basicOpen, Set.mem_ofPred_eq, Order.Ideal.principal_le_iff]
    have hPopen := hPQ.mem_open (isOpen_basicOpen _) hQopen
    exact hPopen (Order.Ideal.principal_le_iff.mpr haP)
  · intro hPQ
    rw [specializes_iff_forall_open]
    intro U hU hQU
    obtain ⟨I, rfl⟩ := isOpen_iff_exists_basicOpen U |>.mp hU
    intro hIP
    exact hQU (hIP.trans hPQ)

/-- In complementary-filter form, specialization reverses inclusion. -/
theorem specializes_iff_primeFilter_ge (P Q : PrimeIdealSpectrum A) :
    P ⤳ Q ↔ primeFilter Q ≤ primeFilter P := by
  rw [specializes_iff_ideal_le]
  constructor
  · intro hPQ a haQ haP
    exact haQ (hPQ haP)
  · intro hQP a haP
    by_contra haQ
    exact (hQP (mem_primeFilter Q a |>.mpr haQ)) haP

private theorem le_of_basicOpen_subset {I J : Order.Ideal A}
    (h : basicOpen I ⊆ basicOpen J) : I ≤ J := by
  intro a haI
  by_contra haJ
  let F : Order.PFilter A := Order.PFilter.principal a
  have hFJ : Disjoint (F : Set A) (J : Set A) := by
    apply Set.disjoint_left.mpr
    intro x hxF hxJ
    apply haJ
    exact J.lower (Order.PFilter.mem_principal.mp hxF) hxJ
  obtain ⟨P, hPprime, hJP, hFP⟩ :=
    DistribLattice.prime_ideal_of_disjoint_filter_ideal hFJ
  let p : PrimeIdealSpectrum A := ⟨P, hPprime⟩
  have haP : a ∉ P := by
    intro haP
    exact Set.disjoint_left.mp hFP
      (show a ∈ F by exact Order.PFilter.mem_principal.mpr le_rfl) haP
  have hpI : p ∈ basicOpen I := by
    intro hIP
    exact haP (hIP haI)
  exact (h hpI) hJP

theorem basicOpen_subset_iff {I J : Order.Ideal A} :
    basicOpen I ⊆ basicOpen J ↔ I ≤ J := by
  constructor
  · exact le_of_basicOpen_subset
  · intro hIJ P hPI hJP
    exact hPI (hIJ.trans hJP)

private def idealToOpen (I : Order.Ideal A) :
    TopologicalSpace.Opens (PrimeIdealSpectrum A) :=
  ⟨basicOpen I, isOpen_basicOpen I⟩

private def idealToOpenEmbedding :
    Order.Ideal A ↪o TopologicalSpace.Opens (PrimeIdealSpectrum A) where
  toFun := idealToOpen
  inj' I J h := by
    have hsets : basicOpen I = basicOpen J :=
      congrArg (fun U : TopologicalSpace.Opens (PrimeIdealSpectrum A) ↦
        (U : Set (PrimeIdealSpectrum A))) h
    apply le_antisymm
    · apply basicOpen_subset_iff.mp
      rw [hsets]
    · apply basicOpen_subset_iff.mp
      rw [hsets.symm]
  map_rel_iff' := basicOpen_subset_iff

private theorem idealToOpen_surjective : Function.Surjective (idealToOpen (A := A)) := by
  intro U
  obtain ⟨I, hI⟩ := isOpen_iff_exists_basicOpen (U : Set (PrimeIdealSpectrum A)) |>.mp U.2
  refine ⟨I, ?_⟩
  apply TopologicalSpace.Opens.ext
  exact hI

/-- The order isomorphism `Id(A) ≃ Ouv(Spec A)`, sending `I` to `D(I)`;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(1). -/
noncomputable def idealOpenOrderIso :
    Order.Ideal A ≃o TopologicalSpace.Opens (PrimeIdealSpectrum A) :=
  OrderIso.ofSurjective idealToOpenEmbedding idealToOpen_surjective

private theorem isCompactElement_of_orderIso_image
    {L M : Type*} [CompleteLattice L] [CompleteLattice M]
    (e : L ≃o M) {a : L} (ha : IsCompactElement (e a)) : IsCompactElement a := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at ha ⊢
  intro S hSne hSdir haS
  have hImageNe : (e '' S).Nonempty := hSne.image e
  have hImageDir : DirectedOn (· ≤ ·) (e '' S) := by
    rintro _ ⟨x, hxS, rfl⟩ _ ⟨y, hyS, rfl⟩
    obtain ⟨z, hzS, hxz, hyz⟩ := hSdir x hxS y hyS
    exact ⟨e z, ⟨z, hzS, rfl⟩, e.monotone hxz, e.monotone hyz⟩
  have hae : e a ≤ sSup (e '' S) := by
    rw [sSup_image, ← e.map_sSup S]
    exact e.monotone haS
  obtain ⟨_, ⟨x, hxS, rfl⟩, hax⟩ := ha (e '' S) hImageNe hImageDir hae
  exact ⟨x, hxS, e.map_rel_iff.mp hax⟩

private theorem isCompactElement_orderIso_iff
    {L M : Type*} [CompleteLattice L] [CompleteLattice M]
    (e : L ≃o M) (a : L) : IsCompactElement (e a) ↔ IsCompactElement a := by
  constructor
  · exact isCompactElement_of_orderIso_image e
  · intro ha
    have hsource : IsCompactElement (e.symm (e a)) := by simpa using ha
    exact isCompactElement_of_orderIso_image e.symm hsource

/-- A basic open `D(I)` is quasi-compact exactly when `I` is principal;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(1),
using the compact-principal theorem from *Ideal Completion*. -/
theorem isCompact_basicOpen_iff (I : Order.Ideal A) :
    IsCompact (basicOpen I) ↔ ∃ a : A, I = Order.Ideal.principal a := by
  change IsCompact ((idealToOpen I : TopologicalSpace.Opens (PrimeIdealSpectrum A)) :
    Set (PrimeIdealSpectrum A)) ↔ _
  rw [← TopologicalSpace.Opens.isCompactElement_iff (idealToOpen I)]
  change IsCompactElement (idealOpenOrderIso I) ↔ _
  rw [isCompactElement_orderIso_iff, Order.Ideal.isCompactElement_iff_eq_principal]

/-- The principal basic opens form a basis of the prime-spectrum topology. -/
theorem isTopologicalBasis_basicOpen_principal :
    IsTopologicalBasis
      (Set.range (fun a : A ↦ basicOpen (Order.Ideal.principal a))) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact isOpen_basicOpen _
  · intro P U hPU hU
    obtain ⟨I, rfl⟩ := isOpen_iff_exists_basicOpen U |>.mp hU
    obtain ⟨a, haI, haP⟩ := exists_mem_not_mem_of_not_le hPU
    refine ⟨basicOpen (Order.Ideal.principal a), ⟨a, rfl⟩, ?_, ?_⟩
    · simpa only [basicOpen, Set.mem_ofPred_eq, Order.Ideal.principal_le_iff] using haP
    · exact basicOpen_subset_iff.mpr (Order.Ideal.principal_le_iff.mpr haI)

private theorem isCompact_basicOpen_principal (a : A) :
    IsCompact (basicOpen (Order.Ideal.principal a)) :=
  isCompact_basicOpen_iff _ |>.mpr ⟨a, rfl⟩

instance instPrespectralSpace : PrespectralSpace (PrimeIdealSpectrum A) :=
  PrespectralSpace.of_isTopologicalBasis' isTopologicalBasis_basicOpen_principal
    isCompact_basicOpen_principal

private theorem basicOpen_principal_inter (a b : A) :
    basicOpen (Order.Ideal.principal a) ∩ basicOpen (Order.Ideal.principal b) =
      basicOpen (Order.Ideal.principal (a ⊓ b)) := by
  ext P
  simp only [basicOpen, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Order.Ideal.principal_le_iff]
  constructor
  · rintro ⟨haP, hbP⟩ habP
    exact (P.2.mem_or_mem habP).elim haP hbP
  · intro habP
    constructor
    · intro haP
      exact habP (P.1.lower inf_le_left haP)
    · intro hbP
      exact habP (P.1.lower inf_le_right hbP)

instance instQuasiSeparatedSpace : QuasiSeparatedSpace (PrimeIdealSpectrum A) :=
  QuasiSeparatedSpace.of_isTopologicalBasis isTopologicalBasis_basicOpen_principal
    fun a b ↦ by
      rw [basicOpen_principal_inter]
      exact isCompact_basicOpen_principal _

instance instCompactSpace : CompactSpace (PrimeIdealSpectrum A) where
  isCompact_univ := by
    have htop : basicOpen (Order.Ideal.principal (⊤ : A)) = Set.univ := by
      ext P
      constructor
      · intro _
        trivial
      · intro _ hle
        exact P.2.top_notMem (Order.Ideal.principal_le_iff.mp hle)
    rw [← htop]
    exact isCompact_basicOpen_principal _

instance instT0Space : T0Space (PrimeIdealSpectrum A) where
  t0 {P Q} hPQ := by
    apply Subtype.ext
    apply Order.Ideal.ext
    ext a
    have hsep := inseparable_iff_forall_isOpen.mp hPQ
      (basicOpen (Order.Ideal.principal a)) (isOpen_basicOpen _)
    change (¬ Order.Ideal.principal a ≤ P.1) ↔
      (¬ Order.Ideal.principal a ≤ Q.1) at hsep
    change a ∈ P.1 ↔ a ∈ Q.1
    simpa only [Order.Ideal.principal_le_iff, Classical.not_not] using not_congr hsep

private def intersectionIdeal (Z : Set (PrimeIdealSpectrum A)) : Order.Ideal A where
  carrier := {a | ∀ P ∈ Z, a ∈ P.1}
  nonempty' := ⟨⊥, fun P _ ↦ P.1.bot_mem⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    intro P hPZ
    exact Order.Ideal.sup_mem (ha P hPZ) (hb P hPZ)
  lower' := by
    intro a b hba ha P hPZ
    exact P.1.lower hba (ha P hPZ)

private theorem intersectionIdeal_isPrime {Z : Set (PrimeIdealSpectrum A)}
    (hZ : IsIrreducible Z) : (intersectionIdeal Z).IsPrime := by
  let _ : (intersectionIdeal Z).IsProper := Order.Ideal.isProper_of_notMem (by
    obtain ⟨P, hPZ⟩ := hZ.nonempty
    intro htop
    exact P.2.top_notMem (htop P hPZ))
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro a b hab
  by_contra hn
  push Not at hn
  obtain ⟨ha, hb⟩ := hn
  change ¬ ∀ P ∈ Z, a ∈ P.1 at ha
  change ¬ ∀ P ∈ Z, b ∈ P.1 at hb
  push Not at ha hb
  obtain ⟨Pa, hPaZ, haPa⟩ := ha
  obtain ⟨Pb, hPbZ, hbPb⟩ := hb
  have hZa : (Z ∩ basicOpen (Order.Ideal.principal a)).Nonempty :=
    ⟨Pa, hPaZ, by simpa only [basicOpen, Set.mem_ofPred_eq,
      Order.Ideal.principal_le_iff] using haPa⟩
  have hZb : (Z ∩ basicOpen (Order.Ideal.principal b)).Nonempty :=
    ⟨Pb, hPbZ, by simpa only [basicOpen, Set.mem_ofPred_eq,
      Order.Ideal.principal_le_iff] using hbPb⟩
  obtain ⟨P, hPZ, hPa, hPb⟩ := hZ.isPreirreducible
    (basicOpen (Order.Ideal.principal a)) (basicOpen (Order.Ideal.principal b))
    (isOpen_basicOpen _) (isOpen_basicOpen _) hZa hZb
  have haP : a ∉ P.1 := by
    simpa only [basicOpen, Set.mem_ofPred_eq, Order.Ideal.principal_le_iff] using hPa
  have hbP : b ∉ P.1 := by
    simpa only [basicOpen, Set.mem_ofPred_eq, Order.Ideal.principal_le_iff] using hPb
  exact (P.2.mem_or_mem (hab P hPZ)).elim haP hbP

private def irreducibleGenericPoint {Z : Set (PrimeIdealSpectrum A)}
    (hZ : IsIrreducible Z) : PrimeIdealSpectrum A :=
  ⟨intersectionIdeal Z, intersectionIdeal_isPrime hZ⟩

private theorem intersectionIdeal_le_of_mem {Z : Set (PrimeIdealSpectrum A)}
    {P : PrimeIdealSpectrum A} (hPZ : P ∈ Z) : intersectionIdeal Z ≤ P.1 := by
  intro a ha
  exact ha P hPZ

private theorem irreducibleGenericPoint_mem {Z : Set (PrimeIdealSpectrum A)}
    (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) : irreducibleGenericPoint hZ ∈ Z := by
  by_contra hpZ
  have hOpen : IsOpen (Zᶜ) := hZclosed.isOpen_compl
  obtain ⟨I, hI⟩ := isOpen_iff_exists_basicOpen (Zᶜ) |>.mp hOpen
  have hpDI : irreducibleGenericPoint hZ ∈ basicOpen I := by
    rw [hI]
    exact hpZ
  obtain ⟨a, haI, haP⟩ := exists_mem_not_mem_of_not_le hpDI
  change ¬ ∀ Q ∈ Z, a ∈ Q.1 at haP
  push Not at haP
  obtain ⟨Q, hQZ, haQ⟩ := haP
  have hQDI : Q ∈ basicOpen I := by
    intro hIQ
    exact haQ (hIQ haI)
  have hQcompl : Q ∈ Zᶜ := by
    rw [← hI]
    exact hQDI
  exact hQcompl hQZ

private theorem irreducibleGenericPoint_isGeneric {Z : Set (PrimeIdealSpectrum A)}
    (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    IsGenericPoint (irreducibleGenericPoint hZ) Z := by
  rw [isGenericPoint_iff_forall_closed hZclosed
    (irreducibleGenericPoint_mem hZ hZclosed)]
  intro W hWclosed hpW Q hQZ
  by_contra hQW
  have hOpen : IsOpen (Wᶜ) := hWclosed.isOpen_compl
  obtain ⟨I, hI⟩ := isOpen_iff_exists_basicOpen (Wᶜ) |>.mp hOpen
  have hQDI : Q ∈ basicOpen I := by
    rw [hI]
    exact hQW
  have hpDI : irreducibleGenericPoint hZ ∈ basicOpen I := by
    intro hIP
    exact hQDI (hIP.trans (intersectionIdeal_le_of_mem hQZ))
  have hpCompl : irreducibleGenericPoint hZ ∈ Wᶜ := by
    rw [← hI]
    exact hpDI
  exact hpCompl hpW

instance instQuasiSober : QuasiSober (PrimeIdealSpectrum A) where
  sober hZ hZclosed := ⟨irreducibleGenericPoint hZ,
    irreducibleGenericPoint_isGeneric hZ hZclosed⟩

/-- The prime-ideal spectrum of a bounded distributive lattice is spectral;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(1). -/
instance instSpectralSpace : SpectralSpace (PrimeIdealSpectrum A) where

end PrimeIdealSpectrum

end SpectralStoneDuality
