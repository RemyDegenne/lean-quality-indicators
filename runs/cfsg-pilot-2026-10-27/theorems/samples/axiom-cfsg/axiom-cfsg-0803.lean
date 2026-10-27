public section

namespace CFSG.StandardType.E6OutdiagPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.Timmesfeld.ExceptionalOrders

theorem ggE6ToralFixNoPpdInput_holds :
    GGE6ToralFixNoPpdInput := by
  intro f hf _ α hα1 hα3 htor r ⟨e, he, hr⟩ z hz hfix
  classical
  obtain ⟨c, hc⟩ := htor
  obtain ⟨b, hb⟩ := hc α (Subgroup.mem_zpowers α)
  have hb3 : ∀ j, b j ^ 3 = 1 := by
    have h : rootDiagAutHom Tag.E6 (GaloisField 2 f) (b ^ 3) = rootDiagAutHom Tag.E6 (GaloisField 2 f) 1 := by
      rw [map_pow, hb, map_one]
      calc (MulAut.conj c * α * (MulAut.conj c)⁻¹) ^ 3 = MulAut.conj c * α ^ 3 * (MulAut.conj c)⁻¹ := by
            rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
        _ = 1 := by rw [hα3, mul_one, mul_inv_cancel]
    intro j
    have h' := congrFun (rootDiagAutHom_injective h) j
    rwa [Pi.pow_apply, Pi.one_apply] at h'
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hα1
    rw [map_one] at hb
    calc α = (MulAut.conj c)⁻¹ * (MulAut.conj c * α * (MulAut.conj c)⁻¹) * MulAut.conj c := by group
      _ = 1 := by rw [← hb]; group
  have hz' : c * z * c⁻¹ ∈ LayerSixE.famCentralizer (τ := Tag.E6) (K := GaloisField 2 f) {b} := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have h1 : rootDiagAutHom Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) = c * z * c⁻¹ := by
      rw [hb, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
      rw [show c⁻¹ * (c * z * c⁻¹) * c = z by group, hfix]
    have h2 := congrArg Subtype.val h1
    rwa [show (rootDiagAutHom Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) :
        adjointGroup Tag.E6 (GaloisField 2 f)) = rootDiagAut Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) from rfl,
      coe_rootDiagAut] at h2
  have hord : orderOf (⟨c * z * c⁻¹, hz'⟩ :
      LayerSixE.famCentralizer (τ := Tag.E6) (K := GaloisField 2 f) {b}) = r := by
    rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  exact not_dvd_card_famCentralizer_of_ppd (GaloisField.card 2 f (by omega)) hb3 hb1 he hr
    (hord ▸ orderOf_dvd_natCard _)

end CFSG.StandardType.E6OutdiagPpd
end
