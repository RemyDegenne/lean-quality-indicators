public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

variable {ι : V → Submodule K W} {A : Submodule K W}

namespace IsLocalAt

theorem sup_line (hP : IsGeneralizedPolygon Γ 4) (hι : IsProjGQ c ι A) [FiniteDimensional K A]
    {p : V} (hp : c p = 0) {U : Submodule K W} (hU : U ≤ A) (hUloc : IsLocalAt c ι p U)
    {L : V} (hpL : Γ.Adj p L) : IsLocalAt c ι p (U ⊔ ι L) := by
  classical
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  have hpLle : ι p ≤ ι L := (hι.adj_iff p L hp hL1).1 hpL
  have hUA : U ⊔ ι L ≤ A := sup_le hU (hι.le_ambient L)
  haveI : FiniteDimensional K ↥(U ⊔ ι L) := Submodule.finiteDimensional_of_le hUA
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  haveI : FiniteDimensional K (ι L) := Submodule.finiteDimensional_of_le (hι.le_ambient L)
  refine ⟨hUloc.1.trans le_sup_left, ?_⟩
  intro z hz
  by_cases hLU : ι L ≤ U
  · have hsup : U ⊔ ι L = U := sup_eq_left.mpr hLU
    exact hUloc.2 (hsup ▸ hz)
  · have hdim : finrank K ↥(U ⊔ ι L) = finrank K U + 1 :=
      finrank_sup_line_eq_succ hι hp hUloc.1 hpL hLU hU
    by_contra hznot
    have hdist : ¬ Γ.dist z p ≤ 2 := by
      intro hle
      exact hznot ⟨hz.1, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hle⟩
    have hzp : z ≠ p := by
      rintro rfl
      exact hdist (by simp)
    have hnotzL : ¬ Γ.Adj z L := fun hzL =>
      hdist ((mem_ptPerp_of_adj_of_adj hz.1 hpL hzL).2 p rfl)
    obtain ⟨y, ⟨hLy, hzy⟩, -⟩ := existsUnique_proj_of_not_adj hP hz.1 hL1 hnotzL
    have hy0 : c y = 0 := color_eq_zero_of_dist_eq_two hP hz.1 hzy
    have hyp : y ≠ p := by
      intro h
      rw [h] at hzy
      exact hdist hzy.le
    have hzyne : z ≠ y := by
      rintro rfl
      simp at hzy
    let M := commonNeighbor hP hzy
    have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzy
    have hyM : Γ.Adj y M := commonNeighbor_adj_right hP hzy
    have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz.1 hzM
    have hM2 : finrank K (ι M) = 2 := hι.finrank_line M hM1
    have hMeq : ι M = ι z ⊔ ι y :=
      line_eq_sup_of_two_adjacent_points hι hz.1 hy0 hzyne hzM hyM
    have hMle : ι M ≤ U ⊔ ι L := by
      rw [hMeq]
      exact sup_le hz.2 (((hι.adj_iff y L hy0 hL1).1 hLy.symm).trans le_sup_right)
    have hpM : ¬ Γ.Adj p M := by
      intro hpM'
      have hML : M = L := eq_of_two_common_points hP (Ne.symm hyp) hpM'.symm hyM.symm hpL.symm hLy
      exact hnotzL (hML ▸ hzM)
    have hlt : finrank K ↥(U ⊔ ι L) < finrank K (ι M) + finrank K U := by
      rw [hdim, hM2]
      omega
    obtain ⟨P, hP1, hPle⟩ :=
      exists_finrank_eq_one_le_inf (X := ι M) (Y := U) (Z := U ⊔ ι L) hMle le_sup_left hlt
    have hPne : P ≠ ⊥ := by
      intro hPbot
      rw [hPbot, finrank_bot] at hP1
      omega
    have hinfne : ι M ⊓ U ≠ ⊥ := by
      intro hbot
      exact hPne (le_antisymm (hbot ▸ hPle) bot_le)
    obtain ⟨x, hMx, hxU⟩ := exists_adj_le_of_line_inf_ne_bot hι hM1 hinfne
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hM1 hMx
    have hxloc : x ∈ ptPerp Γ c {p} := hUloc.2 ⟨hx0, hxU⟩
    have hxp : x ≠ p := by
      intro h
      exact hpM (h ▸ hMx.symm)
    have hxp2 : Γ.dist x p = 2 :=
      dist_eq_two_of_le_two_of_ne hP hx0 hp hxp (hxloc.2 p rfl)
    have hxy : x = y := by
      by_contra hne
      have hxy2 : Γ.dist x y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hMx.symm hyM.symm hne
      have hyp2 : Γ.dist y p = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hLy.symm hpL.symm hyp
      obtain ⟨w, ⟨hxw, hyw, hpw⟩, -⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy2 hxp2 hyp2
      have hwM : w = M :=
        (existsUnique_commonNeighbor hP hxy2).unique ⟨hxw, hyw⟩ ⟨hMx.symm, hyM⟩
      exact hpM (hwM ▸ hpw)
    have hyU : ι y ≤ U := hxy ▸ hxU
    have hLle : ι L ≤ U := by
      rw [line_eq_sup_of_two_adjacent_points hι hp hy0 (Ne.symm hyp) hpL hLy.symm]
      exact sup_le hUloc.1 hyU
    exact hLU hLle

end IsLocalAt
end CFSG.Geometry.GeneralizedQuadrangles
end
