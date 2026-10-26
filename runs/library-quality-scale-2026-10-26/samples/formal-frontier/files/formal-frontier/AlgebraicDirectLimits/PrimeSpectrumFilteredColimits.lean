/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Prime spectra of filtered colimits of commutative rings

The spectrum of a filtered colimit of commutative rings is the inverse limit of the
spectra, in the category of topological spaces. The canonical projections contract
prime ideals along the ring cocone maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace PrimeSpectrum

variable {J : Type v} [SmallCategory J]
variable (F : J ⥤ CommRingCat.{max v u}) (c : Cocone F)

/-- The cone of spectra induced by a cocone of commutative rings. -/
noncomputable def colimitCone : Cone (F.op ⋙ AlgebraicGeometry.Spec.toTop) :=
  AlgebraicGeometry.Spec.toTop.mapCone c.op

/-- The point of the induced cone is the spectrum of the cocone ring. -/
@[simp]
theorem colimitCone_pt : (colimitCone F c).pt = AlgebraicGeometry.Spec.topObj c.pt := rfl

/-- Each projection of the induced cone contracts along the corresponding cocone map. -/
@[simp]
theorem colimitCone_π_apply (j : J) (p : PrimeSpectrum c.pt) :
    (colimitCone F c).π.app (op j) p = comap (c.ι.app j).hom p := by
  rfl

/-- Compatible tuples of prime ideals in a ring diagram, viewed as sections of spectra. -/
abbrev spectrumSections (F : J ⥤ CommRingCat.{max v u}) :=
  ((F.op ⋙ AlgebraicGeometry.Spec.toTop) ⋙ forget TopCat).sections

private instance forget_preservesColimit [IsFiltered J] :
    PreservesColimit F (forget CommRingCat.{max v u}) :=
  ((preservesFilteredColimitsOfSize_shrink
    (forget CommRingCat.{max v u})).preserves_filtered_colimits J).preservesColimit

theorem section_mem_map (s : spectrumSections F)
    {i j : J} (f : i ⟶ j) (a : F.obj i) :
    a ∈ (s.val (op i)).asIdeal ↔ (F.map f).hom a ∈ (s.val (op j)).asIdeal := by
  have h : comap (F.map f).hom (s.val (op j)) = s.val (op i) := by
    have hs := s.property f.op
    change comap (F.map f).hom (s.val (op j)) = s.val (op i) at hs
    exact hs
  rw [← h]
  rfl

theorem section_mem_of_eq [IsFiltered J] (hc : IsColimit c)
    (s : spectrumSections F) {i j : J} {a : F.obj i} {b : F.obj j}
    (h : (c.ι.app i).hom a = (c.ι.app j).hom b) :
    a ∈ (s.val (op i)).asIdeal ↔ b ∈ (s.val (op j)).asIdeal := by
  have htype : IsColimit ((forget CommRingCat).mapCocone c) :=
    ((((preservesFilteredColimitsOfSize_shrink
      (forget CommRingCat.{max v u})).preserves_filtered_colimits J).preservesColimit).preserves
      hc).some
  obtain ⟨k, f, g, heq⟩ := (Types.FilteredColimit.isColimit_eq_iff _ htype).mp h
  change (F.map f).hom a = (F.map g).hom b at heq
  rw [section_mem_map F s f, section_mem_map F s g, heq]

/-- The ideal of a filtered ring colimit determined by a compatible family of prime ideals. -/
def idealOfSection [IsFiltered J] (hc : IsColimit c) (s : spectrumSections F) :
    Ideal c.pt where
  carrier := {x | ∃ (j : J) (a : F.obj j), (c.ι.app j).hom a = x ∧
    a ∈ (s.val (op j)).asIdeal}
  zero_mem' := by
    let j : J := IsFiltered.nonempty.some
    exact ⟨j, 0, map_zero _, (s.val (op j)).asIdeal.zero_mem⟩
  add_mem' := by
    rintro x y ⟨i, a, rfl, ha⟩ ⟨j, b, rfl, hb⟩
    let k := IsFiltered.max i j
    let f := IsFiltered.leftToMax i j
    let g := IsFiltered.rightToMax i j
    refine ⟨k, (F.map f).hom a + (F.map g).hom b, ?_, ?_⟩
    · rw [map_add, Cocone.w_apply c f a, Cocone.w_apply c g b]
    · exact (s.val (op k)).asIdeal.add_mem
        ((section_mem_map F s f a).mp ha) ((section_mem_map F s g b).mp hb)
  smul_mem' := by
    rintro x y ⟨j, b, rfl, hb⟩
    obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    let k := IsFiltered.max i j
    let f := IsFiltered.leftToMax i j
    let g := IsFiltered.rightToMax i j
    refine ⟨k, (F.map f).hom a * (F.map g).hom b, ?_, ?_⟩
    · rw [smul_eq_mul, map_mul, Cocone.w_apply c f a, Cocone.w_apply c g b]
    · exact (s.val (op k)).asIdeal.mul_mem_left _ ((section_mem_map F s g b).mp hb)

@[simp] theorem mem_idealOfSection_iff [IsFiltered J] (hc : IsColimit c)
    (s : spectrumSections F) (j : J) (a : F.obj j) :
    (c.ι.app j).hom a ∈ idealOfSection F c hc s ↔ a ∈ (s.val (op j)).asIdeal := by
  constructor
  · rintro ⟨i, b, h, hb⟩
    exact (section_mem_of_eq F c hc s h.symm).mpr hb
  · exact fun ha ↦ ⟨j, a, rfl, ha⟩

theorem idealOfSection_isPrime [IsFiltered J] (hc : IsColimit c)
    (s : spectrumSections F) : (idealOfSection F c hc s).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    let j : J := IsFiltered.nonempty.some
    have h : (1 : c.pt) ∈ idealOfSection F c hc s := htop ▸ Submodule.mem_top
    rw [← map_one (c.ι.app j).hom, mem_idealOfSection_iff F c hc s j] at h
    exact (s.val (op j)).isPrime.one_notMem h
  · intro x y hxy
    obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep F hc x
    obtain ⟨j, b, hb⟩ := Concrete.isColimit_exists_rep F hc y
    let k := IsFiltered.max i j
    let f := IsFiltered.leftToMax i j
    let g := IsFiltered.rightToMax i j
    have h : (F.map f).hom a * (F.map g).hom b ∈ (s.val (op k)).asIdeal := by
      apply (mem_idealOfSection_iff F c hc s k _).mp
      rw [map_mul, Cocone.w_apply c f a, Cocone.w_apply c g b, ha, hb]
      exact hxy
    rcases (s.val (op k)).isPrime.mem_or_mem h with h | h
    · left
      rw [← ha]
      exact (mem_idealOfSection_iff F c hc s i a).mpr
        ((section_mem_map F s f a).mpr h)
    · right
      rw [← hb]
      exact (mem_idealOfSection_iff F c hc s j b).mpr
        ((section_mem_map F s g b).mpr h)

/-- The prime ideal of a filtered ring colimit specified by a compatible family of primes. -/
def pointOfSection [IsFiltered J] (hc : IsColimit c)
    (s : spectrumSections F) : PrimeSpectrum c.pt :=
  ⟨idealOfSection F c hc s, idealOfSection_isPrime F c hc s⟩

@[simp] theorem pointOfSection_proj [IsFiltered J] (hc : IsColimit c)
    (s : spectrumSections F) (j : J) :
    comap (c.ι.app j).hom (pointOfSection F c hc s) = s.val (op j) := by
  ext a
  exact mem_idealOfSection_iff F c hc s j a

/-- A filtered ring-colimit cocone induces a limit cone of prime spectra in `TopCat`. -/
noncomputable def colimitCone_isLimit [IsFiltered J] (hc : IsColimit c) :
    IsLimit (colimitCone F c) := by
  letI : PreservesColimit F (forget CommRingCat.{max v u}) :=
    ((preservesFilteredColimitsOfSize_shrink
      (forget CommRingCat.{max v u})).preserves_filtered_colimits J).preservesColimit
  have hset : IsLimit ((forget TopCat).mapCone (colimitCone F c)) := by
    refine Classical.choice ((Types.isLimit_iff_bijective_sectionOfCone _).mpr ?_)
    constructor
    · intro p q hpq
      apply PrimeSpectrum.ext
      ext x
      obtain ⟨j, a, rfl⟩ := Concrete.isColimit_exists_rep F hc x
      have h := congrArg (fun s : spectrumSections F ↦ s.val (op j)) hpq
      change comap (c.ι.app j).hom p = comap (c.ι.app j).hom q at h
      change a ∈ (comap (c.ι.app j).hom p).asIdeal ↔
        a ∈ (comap (c.ι.app j).hom q).asIdeal
      rw [h]
    · intro s
      refine ⟨pointOfSection F c hc s, ?_⟩
      apply Subtype.ext
      funext j
      cases j with
      | op j => exact pointOfSection_proj F c hc s j
  refine Classical.choice ((TopCat.nonempty_isLimit_iff_eq_induced _ hset).mpr ?_)
  apply le_antisymm
  · apply le_iInf
    intro j
    exact continuous_iff_le_induced.mp ((colimitCone F c).π.app j).hom.continuous
  · change _ ≤ (inferInstance : TopologicalSpace (PrimeSpectrum c.pt))
    rw [PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom]
    apply le_generateFrom
    rintro _ ⟨a, rfl⟩
    obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep F hc a
    let x : c.pt := (c.ι.app j).hom b
    have h : (↑(basicOpen x) : Set (PrimeSpectrum c.pt)) =
        (colimitCone F c).π.app (op j) ⁻¹' (basicOpen b : Set (PrimeSpectrum (F.obj j))) := by
      ext p
      change x ∉ p.asIdeal ↔ (c.ι.app j).hom b ∉ p.asIdeal
      rfl
    have hOpen : @IsOpen (PrimeSpectrum c.pt)
        (⨅ k, ((F.op ⋙ AlgebraicGeometry.Spec.toTop).obj k).str.induced
          ((colimitCone F c).π.app k))
        (↑(basicOpen x) : Set (PrimeSpectrum c.pt)) := by
      rw [h]
      exact (isOpen_induced (isOpen_basicOpen (a := b))).mono
        (iInf_le _ (op j))
    exact hOpen

variable [IsFiltered J]

/-- The spectrum of a filtered colimit is homeomorphic to the chosen limit of spectra. -/
noncomputable def colimitHomeomorph (hc : IsColimit c) :
    PrimeSpectrum c.pt ≃ₜ ↥(limit (F.op ⋙ AlgebraicGeometry.Spec.toTop) : TopCat) :=
  TopCat.homeoOfIso <|
    IsLimit.conePointUniqueUpToIso (colimitCone_isLimit F c hc)
      (limit.isLimit (F.op ⋙ AlgebraicGeometry.Spec.toTop))

/-- The homeomorphism to the chosen limit agrees with contraction at each stage. -/
@[simp]
theorem colimitHomeomorph_π_apply (hc : IsColimit c) (j : J)
    (p : PrimeSpectrum c.pt) :
    limit.π (F.op ⋙ AlgebraicGeometry.Spec.toTop) (op j)
      (colimitHomeomorph F c hc p) = comap (c.ι.app j).hom p := by
  change ((IsLimit.conePointUniqueUpToIso (colimitCone_isLimit F c hc)
    (limit.isLimit (F.op ⋙ AlgebraicGeometry.Spec.toTop))).hom ≫
      limit.π (F.op ⋙ AlgebraicGeometry.Spec.toTop) (op j)) p = _
  rw [limit.conePointUniqueUpToIso_hom_comp]
  exact colimitCone_π_apply F c j p

end PrimeSpectrum
