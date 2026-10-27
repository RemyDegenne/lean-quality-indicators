public section

namespace CFSG.Quasithin

namespace F6

section SettingSQT

theorem isStronglyQuasithin_of_isQuasisimple (hQ : NativeSQTSection) {D X : Type} [Group D]
    [Group X] [Finite X] (hX : CFSG.SectionRank.IsSQTKCat X) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X)
    {L : Subgroup D} (hq : CFSG.IsQuasisimple ↥L) :
    CFSG.IsStronglyQuasithin (↥L ⧸ Subgroup.center ↥L) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  set H : Subgroup X := (L.map e.toMonoidHom).comap π with hH
  have hmemL : ∀ h : ↥H, e.symm (π h) ∈ L := by
    intro h
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp h.2)
    have : e.symm (π h) = l := by
      rw [← hle]
      exact e.symm_apply_apply l
    rw [this]
    exact hl
  let ψ : ↥H →* ↥L :=
    (e.symm.toMonoidHom.comp (π.comp H.subtype)).codRestrict L hmemL
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 X) (e l)
    have hxH : x ∈ H := by
      rw [hH, Subgroup.mem_comap, hx]
      exact Subgroup.mem_map_of_mem _ l.2
    refine ⟨⟨x, hxH⟩, Subtype.ext ?_⟩
    change e.symm (π x) = l
    rw [hx, MulEquiv.symm_apply_apply]
  let φ : ↥H →* ↥L ⧸ Subgroup.center ↥L := (QuotientGroup.mk' (Subgroup.center ↥L)).comp ψ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  let iso : ↥H ⧸ φ.ker ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have : IsSimpleGroup (↥H ⧸ φ.ker) := iso.isSimpleGroup
  have hnonab : ∃ a b : ↥H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
    have := congrArg iso h
    simpa using this
  have : Finite D := Finite.of_equiv _ e.symm.toEquiv
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv iso.symm (hQ X hX H φ.ker hnonab)

end SettingSQT
end F6
end CFSG.Quasithin
end
