namespace P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

p2m_open

namespace Place

p2m_open

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')

variable (hne : w.toValuationSubring.comap (algebraMap F F') ≠ ⊤)

include hne

theorem irreducible_mk_comap' {g : F} (hg0 : g ≠ 0)
    (hmem : g ∈ w.toValuationSubring.comap (algebraMap F F'))
    (hge : w.ord (algebraMap F F' g) = comapRamIdx (F := F) w) :
    Irreducible (⟨g, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) := by
  have hepos : 0 < comapRamIdx (F := F) w := w.comapRamIdx_pos (F := F) hne
  constructor
  ·
    rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  ·

    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : g = a * b := by simpa [Subtype.ext_iff] using hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hsum : w.ord (algebraMap F F' a) + w.ord (algebraMap F F' b)
        = comapRamIdx (F := F) w := by
      rw [← w.ord_mul (algebraMap_ne_zero ha0) (algebraMap_ne_zero hb0), ← map_mul, ← hab',
        hge]
    have ha' : 0 ≤ w.ord (algebraMap F F' a) := (mem_comap_iff_ord_nonneg ha0).mp ha
    have hb' : 0 ≤ w.ord (algebraMap F F' b) := (mem_comap_iff_ord_nonneg hb0).mp hb

    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_mk_comap_iff ha0 ha).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_mk_comap_iff hb0 hb).mpr hb0'.symm)
    exfalso
    have h1 := w.comapRamIdx_le_ord (F := F) ha0 hapos
    have h2 := w.comapRamIdx_le_ord (F := F) hb0 hbpos
    omega

end Restrict
end Place
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
