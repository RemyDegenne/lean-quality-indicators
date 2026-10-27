public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc

theorem coc_std
    {δ : MulAut W11 → W11}
    (hδ : ∀ g ∈ img11 AutPerm, ∀ k ∈ img11 AutPerm, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ (img11 AutPerm) z0, δ r ∈ Subgroup.zpowers z0) :
    ∃ w ∈ vZ (img11 AutPerm) z0, ∀ g ∈ img11 AutPerm, δ g = w * (g w)⁻¹ := by
  rw [radZ_std] at hR
  rw [vZ_std]
  obtain ⟨m, hm, h⟩ := eq_inner_std hδ (p := 0) (z := 31) hR (by norm_num) (by decide)
    img11_le_closure (rho11_mem_img11 _) (rho11_mem_img11 _) actsBy_rhoA actsBy_rhoB coc_lt
    ks_tgt coc_ok w0_lt coc_cert
  exact ⟨toW 11 m, toW_mem_maskSub hm, h⟩

end CFSG.Quasithin.H.Coc24
end
