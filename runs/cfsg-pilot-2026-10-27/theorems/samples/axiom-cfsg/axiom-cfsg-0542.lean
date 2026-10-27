public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint

open CFSG.LocalAnalysis.EvenBN.Common

open CFSG.ABGLocalTools (IsSylowOf)

open scoped MatrixGroups

namespace ProductN1HatAux

section D1Basics

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_leviToBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ∃ ψ : d.leviShort →* H1bar d t, Function.Injective ψ ∧ ψ.range = kBar d t := by
  have hmem : ∀ s : d.leviShort, ((s : L) : G) ∈ cLV d := fun s =>
    ⟨s.1, d.leviShort_le_centralizer_V s.2, rfl⟩
  have hN : ∀ s : d.leviShort, ((s : L) : G) ∈ normalizer (yamadaD₅ d t : Set G) := fun s =>
    cLV_le_normalizer_D5 h d hlay (hmem s)
  let j : d.leviShort →* normalizer (yamadaD₅ d t : Set G) :=
    MonoidHom.codRestrict (L.subtype.comp d.leviShort.subtype) _ hN
  refine ⟨(NormalizerQuotient.proj (yamadaD₅ d t)).comp j, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro s hs
    have hs' : ((s : L) : G) ∈ yamadaD₅ d t := NormalizerQuotient.proj_eq_one_iff.1 hs
    obtain ⟨n, hn, hns⟩ := D5_inf_L_le h d hlay ⟨hs', (s : L).2⟩
    have hn' : n = (s : L) := Subtype.ext hns
    have : (s : L) ∈ d.D ⊓ d.leviShort := ⟨hn' ▸ hn, s.2⟩
    rw [d.D_inf_leviShort, mem_bot] at this
    exact Subtype.ext this
  · ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact NormalizerQuotient.proj_mem_bar (hmem s)
    · rintro ⟨⟨x, hxN⟩, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := mem_subgroupOf.1 hx
      rw [d.centralizer_V_eq] at hl
      obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort hl
      refine ⟨⟨s, hs⟩, ?_⟩
      show NormalizerQuotient.proj (yamadaD₅ d t) ⟨((s : L) : G), hN ⟨s, hs⟩⟩ =
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨L.subtype (n * s), hxN⟩
      rw [NormalizerQuotient.proj_eq_proj_iff]
      show ((s : L) : G)⁻¹ * ((n * s : L) : G) ∈ yamadaD₅ d t
      rw [show ((s : L) : G)⁻¹ * ((n * s : L) : G) = ((s : L) : G)⁻¹ * (n : G) * (s : G) by
        simp [mul_assoc]]
      have h1 := (mem_normalizer_iff.1 (inv_mem (hN ⟨s, hs⟩)) (n : G)).1
        (D_map_le_D5 h d hlay ⟨n, hn, rfl⟩)
      simpa using h1

end D1Basics
end ProductN1HatAux
end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
end
