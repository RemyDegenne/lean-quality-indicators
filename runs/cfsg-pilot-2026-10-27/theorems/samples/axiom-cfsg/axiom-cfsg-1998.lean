public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving.PLType

open CFSG.Open Matrix

theorem nonempty_statedSp_two_mulEquiv_perm_six :
    Nonempty (↥(StatedSp 2 (ZMod 2)) ≃* Equiv.Perm (Fin 6)) := by
  have hmem : ∀ σ : Equiv.Perm (Fin 6), CFSG.Quasithin.H.Sp4A6.psiHom σ ∈ StatedSp 2 (ZMod 2) :=
    fun σ => Subgroup.subset_closure (CFSG.Quasithin.H.Sp4A6.psiMat_symplectic σ)
  let f : Equiv.Perm (Fin 6) →* ↥(StatedSp 2 (ZMod 2)) :=
    (CFSG.Quasithin.H.Sp4A6.psiHom).codRestrict _ hmem
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    apply CFSG.Quasithin.H.Sp4A6.psiMat_eq_one σ
    have h1 : f σ = 1 := hσ
    have h2 : CFSG.Quasithin.H.Sp4A6.psiHom σ = 1 := congrArg Subtype.val h1
    rw [← CFSG.Quasithin.H.Sp4A6.coe_psiHom, h2]
    rfl
  have hcard : Nat.card (Equiv.Perm (Fin 6)) = Nat.card ↥(StatedSp 2 (ZMod 2)) := by
    rw [card_statedSp_two_two, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hbij : Function.Bijective f :=
    (Function.Injective.bijective_of_nat_card_le hinj hcard.ge)
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end CFSG.HardMathSupport.RichardWeiss.Proving.PLType
end
