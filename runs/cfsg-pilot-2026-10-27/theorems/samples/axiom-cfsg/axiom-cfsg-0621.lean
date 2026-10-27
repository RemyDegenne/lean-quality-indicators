public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Quasithin

open scoped commutatorElement

variable {G : Type} [Group G] {E : Subgroup G} {t z : G}

namespace CocodeToData

variable (hm : M24Out G E t) (hz : IsZ E t z)

theorem P_irred (h : CocodeXOf hm hz) :
    ∀ S : Subgroup G, E ≤ S → S ≤ Pg E z → InvUnder (CNz E z) S → S = E ∨ S = Pg E z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro S hES hSP hSinv
  have hPX : TwoFi22.O2In (S44.XE E ⊓ centSub (zpowers (⟨z, hz.1⟩ : ↥E))) ≤ S44.XE E :=
    (O2In_le _).trans inf_le_left
  rw [Pg_eq_preS hm hz.1] at hSP ⊢
  obtain ⟨T, hTX, rfl⟩ := exists_T hm.centralizer_eq hES (hSP.trans (preS_le_Nrm _))
  have hTP := (preS_le_preS_iff hTX).1 hSP
  rw [CNz_eq_preS hm hz.1] at hSinv
  have hinv := (invUnder_preS_preS_iff inf_le_left hTX).1 hSinv
  rcases h.P_irred T hTP hinv with h1 | h1
  · rw [h1]
    exact Or.inl (preS_bot hm.centralizer_eq)
  · rw [h1]
    exact Or.inr rfl

end CocodeToData
end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
end
