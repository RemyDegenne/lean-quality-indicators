public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_dMinDeg_le_mBar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) (h1A : S23_1A D Ch) (hDeg : KMinDegLow)
    {A K P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L) (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hn : NParam (Hinf P) c.n) (hn2 : 2 < c.n) (hshape : S20_7Shape (Bar2 c.L)) :
    ¬ dMinDeg ↥(barSub ⊥ A hA K) ≤ mBar c.N ⊥ A hA := by
  intro hle
  have hKN : K ≤ c.N := (CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)
  have hNbot : c.N ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hKstab : K ≤ stabTil ⊥ A := hKN.trans (le_inf hAN hNbot)
  have h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK
  have hcomp : IsComponentOf (barSub ⊥ A hA K) (Mbar c.N ⊥ A hA) :=
    isComponentOf_barSub_of_sup_conj c h208 h1930 hA hAV hAN hAne hK hgen
  haveI : Nontrivial ↥(barSub ⊥ A hA K) :=
    CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2)
  have hsurj : Function.Surjective (barSubBar2Hom (V₀ := ⊥) hA hKstab h2) :=
    barSubBar2Hom_surjective hA hKstab h2
  have hd1 : dMinDeg (Bar2 K) ≤ dMinDeg ↥(barSub ⊥ A hA K) :=
    dMinDeg_le_of_surjective (barSubBar2Hom (V₀ := ⊥) hA hKstab h2) hsurj
  have hd2 : c.n + 1 < dMinDeg (Bar2 K) :=
    hDeg c.L K P c.n hshape hK hP.1.1 hn hn2
  obtain ⟨hW, hm, ha⟩ :=
    aBar_bound_of_S23_1A c h1A h1930 hA hAV hAne hAN hmin
  have hmle : mBar c.N ⊥ A hA ≤ c.n + 1 :=
    le_trans hm (Nat.add_le_add_right ha 1)
  exact (not_le_of_gt hd2) (le_trans hd1 (le_trans hle hmle))

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
