public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti

open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open scoped commutatorElement

section Plain

variable {G : Type} [Group G] [Finite G]

theorem autSolvThree_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (hT : AutSolvThree T) :
    AutSolvThree S := by
  intro Ē hĒ h9 Y hY
  set Ē' : Subgroup (MulAut T) := Ē.map (MulAut.congr e).toMonoidHom with hĒ'
  have hĒ'ab : IsElemAbelian 3 Ē' := CFSG.SectionRank.isElemAbelian_map hĒ _
  have h9' : 9 ≤ Nat.card Ē' := by
    rw [hĒ', Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact h9
  set Y' : Subgroup T := Y.map e.toMonoidHom with hY'
  have hYfix : ∀ y ∈ Y', ∀ ψ ∈ Ē', ψ y = y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    simp [MulAut.congr_apply, hY y hy ψ hψ]
  haveI := hT Ē' hĒ'ab h9' Y' hYfix
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Y.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.injective _)

end Plain
end CFSG.LocalAnalysis.GLTheoremA.S265C
end
