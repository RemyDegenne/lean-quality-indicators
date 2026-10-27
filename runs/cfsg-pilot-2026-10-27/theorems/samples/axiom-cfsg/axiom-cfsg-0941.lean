public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G]

namespace SemiFam

variable {𝒟 : Set (Subgroup G)} {D : Subgroup G}

section Finite

variable [Finite G]

omit [Finite G] in
theorem exists_proj (h : SemiFam 𝒟) [Fintype ↥𝒟] :
    ∃ π : (i : ↥𝒟) → ↥(sSup 𝒟) →* ↥(i : Subgroup G),
      (∀ i, Function.Surjective (π i)) ∧ ∀ x : ↥(sSup 𝒟), (∀ i, π i x = 1) → x = 1 := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := h.pairwise) h.iSupIndep
  have hr : (Subgroup.noncommPiCoprod h.pairwise).range = sSup 𝒟 := by
    rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']
  set e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  refine ⟨fun i => (Pi.evalMonoidHom (fun j : ↥𝒟 => ↥(j : Subgroup G)) i).comp
    e.symm.toMonoidHom, fun i y => ?_, fun x hx => ?_⟩
  · classical
    refine ⟨e (Pi.mulSingle i y), ?_⟩
    simp
  · have : e.symm x = 1 := funext hx
    simpa using congrArg e this

end Finite
end SemiFam
end CFSG.Quasithin.E2.E22N.E111R
end
