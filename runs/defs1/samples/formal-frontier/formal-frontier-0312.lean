public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

namespace PrimeIdealSpectrum

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

end PrimeIdealSpectrum
end SpectralStoneDuality
end
