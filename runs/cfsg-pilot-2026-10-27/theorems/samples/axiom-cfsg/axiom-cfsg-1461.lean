public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock planeTorus longInv suppGroup coords
  shortBlock planeTorusElt leviCent mat_planeTorusElt planeTorusDiag mat_shortBlock transvOne)

open CFSG.ClassicalInvolution.RouteD.LeviModel

open CFSG.ClassicalInvolution.WeakCT (torusHom coe_torusHom)

open CFSG.LieType.Universal.Symplectic.SpExtras (mat_injective)

open CFSG.LieType.Steinberg.Sp (blockMat)

open scoped MatrixGroups

section Charts

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {Fr : Frame p f 2 Ω K z} {l : Fin 3}

theorem LocalFrameI.not_inf_le_centralizer_levi (S : CSetupW p f 2 Ω K z)
    (LF : LocalFrameI Fr l) (a : (GaloisField p f)ˣ) :
    ¬ (Mf Fr (l.succAbove 0) (l.succAbove 1) ⊓ Subgroup.centralizer
      ({LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
        LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a))} :
        Set G) ≤ Subgroup.centralizer ({Fr.zf (l.succAbove 0)} : Set G)) := by
  intro h
  have hu : LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
      LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) =
      LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a) :=
    (map_mul _ _ _).symm
  rw [hu] at h
  have hmem : LF.layerSp S (shortBlock (GaloisField p f) fin_two_zero_ne_one
      (transvOne (GaloisField p f))) ∈ Mf Fr (l.succAbove 0) (l.succAbove 1) ⊓
        Subgroup.centralizer ({LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a)} :
          Set G) := by
    refine ⟨by rw [← LF.layerSp_range S]; exact ⟨_, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Models.SymplecticPairs.commute_shortBlock_planeTorusElt
      fin_two_zero_ne_one a _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hmem)
  rw [← LF.layerSp_longInv S 0] at hc
  refine Models.SymplecticPairs.not_commute_shortBlock_longInv fin_two_zero_ne_one S.two_ne_zero ?_
  show _ * _ = _ * _
  apply LF.layerSp_injective S
  rw [map_mul, map_mul]
  exact hc

end Charts
end CFSG.ClassicalInvolution.RouteD
end
