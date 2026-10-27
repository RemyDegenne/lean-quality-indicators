public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem exists_chi0 (bs : ℕ) (hpc : MC.PcX (vB bs 0) (vB bs 1) (vB bs 2) (vB bs 3) (vB bs 4)
    (vB bs 5) (vB bs 6) (vB bs 7))
    (hnf : ∀ a : MC, nfProd [vB bs 0, vB bs 1, vB bs 2, vB bs 3, vB bs 4, vB bs 5, vB bs 6,
      vB bs 7] (MC.nfBits a) = if chi0B bs a then Multiplicative.ofAdd 1 else 1) :
    ∃ χ₀ : MC →* Multiplicative (ZMod 2),
      ∀ a, χ₀ a = if chi0B bs a then Multiplicative.ofAdd 1 else 1 := by
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7, h8⟩ := MC.exists_hom hpc
  refine ⟨ι, fun a => ?_⟩
  conv_lhs => rw [MC.nf_spec a]
  rw [map_nfProd]
  simp only [MC.gens, List.map_cons, List.map_nil, h1, h2, h3, h4, h5, h6, h7, h8]
  exact hnf a

end KD8c
end CFSG.OddStandard.SmallF3.L33.KD
end
