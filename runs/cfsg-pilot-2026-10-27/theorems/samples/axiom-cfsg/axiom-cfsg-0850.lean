public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open

open CFSG.Quasithin (perfectCore perfectCore_le)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

open CFSG.SeitzReduction.SeitzQ2 (SwapParam SwapPairExclusion)

open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

section Main

theorem false_of_swapCase_omega_plus_of_swapPairExclusion (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hS : ∀ k : Fin n, ∀ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k) : Set G),
      ∃ Kc : Subgroup (centralizer (modelToG e (pairTorus (K := K) k) : Set G) ⧸
          oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternative (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩)
          (((modelToG e (pairPerp (K := K) k)).subgroupOf
              (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
              Set G))))) Kc m f' ∧
        Kc.map (MulAut.conj (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G)))
              ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hP : SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K))) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X : Fin n → Subgroup G := fun k => modelToG e (pairTorus (K := K) k) with hXdef
  set D : Fin n → Subgroup G := fun k => modelToG e (pairPerp (K := K) k) with hDdef
  have hdata : ∀ k : Fin n, X k ≤ L ∧ t ∈ centralizer (X k : Set G) ∧
      D k ≤ centralizer (X k : Set G) ∧ center (D k) = ⊥ := by
    intro k
    obtain ⟨hXL, htX, -, -, -, -, hDXt, -, hZ, -, -⟩ :=
      neighbour_data_pairTorus hKc hq hn k e htC (X := X k) rfl (D := D k) rfl
    exact ⟨hXL, htX, hDXt.trans inf_le_left, hZ⟩
  have hpar : ∀ k : Fin n, ∃ P : SwapParam t (D k), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (X k) := fun k =>
    exists_swapParam_pairTorus hset hKc hq hn k e htC ht rfl (hdata k).2.1 rfl
      (hS k (hdata k).2.1)
  choose Ψ hinj hrange using hpar
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  have hO' : ∀ a b, perfectCore (D a ⊓ centralizer (X b : Set G)) =
      modelToG e (plusOverlap (K := K) a b) := fun a b =>
    perfectCore_modelToG_inf_centralizer e _ _
  exact false_of_swapParam_pieces hset hOut e hP ht hKt Ψ hinj hrange (fun k => (hdata k).1)
    (fun k => UnitaryPilot.modelToG_le e _) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2)
    (fun a H hH hle => perfect_le_pairPerp_of_le hq e a hH hle)
    (fun a b hab => UnitaryPilot.modelToG_mono e (pairTorus_le_pairPerp hab))
    (fun a b hab => by
      rw [hO']
      exact isSimpleGroup_modelToG e (isSimpleGroup_plusOverlap hq hn hab))
    (fun a b hab => by
      rw [hO']
      exact center_modelToG_eq_bot e (center_plusOverlap_eq_bot hq hn hab))
    ⟨0, by omega⟩
    (fun k l hk hl hkl => by
      rw [hO', hO', hO']
      exact exists_ne_one_mem_modelToG e
        (exists_ne_one_mem_plusOverlap_triple hq hn (Ne.symm hk) (Ne.symm hl) hkl))
    (fun j => (plusNodeSet n j)ᶜ) (compl_plusNodeSet_inter_nonempty hn)
    (le_iSup_perfectCore_pieces hKc hq hn e)

end Main
end CFSG.SeitzReduction.OmegaPilot
end
