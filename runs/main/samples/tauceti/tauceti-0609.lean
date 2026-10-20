public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology

variable {K : Type} [Field K]

section Idele

variable [NumberField K]

section Layer

open NormalLayer

variable (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
  (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
  (χ' : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ))
  (hχ' : ∀ g : AbsoluteGaloisGroup K, χ (.ofMul g) =
    χ' (.ofMul (Abelianization.of
      ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))))
  (a' : (ideleFormation K).level (ofOpenNormal V).ground)

include hχ' in
theorem ideleLayerCorInfl_artinCharacterCup
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffEquivIdeleFormation K (a : IdeleCoeff K) = a') :
    ideleLayerCorInfl K (ofOpenNormal V)
        ((ofOpenNormal V).artinCharacterCup (ideleFormation K) a' χ') =
      (characterCarryCocycle χ hχ a : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) := by
  -- The carry of `χ` at `u, v ∈ G_K` is the carry of `χ'` at their classes in `G_K ⧸ V`.
  have hcarry (u v : (ofOpenNormal V).ground) :
      characterCarry (χ'.comp Abelianization.of.toAdditive) (u : (ofOpenNormal V).Gal) v =
        characterCarry χ (u : AbsoluteGaloisGroup K) v := by
    simpa only [galOfOpenNormalEquiv_symm_mk] using
      characterCarry_galOfOpenNormalEquiv_symm V χ' χ hχ' u v
  rw [ideleLayerCorInfl_apply,
    ← LinearEquiv.apply_symm_apply ((ofOpenNormal V).groundLevelEquiv (ideleFormation K)) a',
    artinCharacterCup_groundLevelEquiv_eq_H2π, NormalLayer.explicitInfl2_H2π]
  -- The inflated layer cocycle is the restriction of the carry cocycle of `χ` to the ground
  -- subgroup `⊤`, and corestriction from `⊤` after restriction is multiplication by the index `1`.
  refine (congrArg (explicitCor2 _ _ _ _) (?_ : _ = explicitRes2 (AbsoluteGaloisGroup K)
    (IdeleCoeff K) _ (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)))).trans ?_
  · rw [explicitRes2_mk]
    congr 1
    refine Subtype.ext (funext fun ⟨u, v⟩ ↦ ?_)
    simp only [inflCocycle2_apply, TauCeti.groupCohomology.characterCarryCocycles₂_apply,
      cocyclesMap2_apply, characterCarryCocycle_apply, AddSubgroupClass.coe_zsmul, map_zsmul,
      AddMonoidHom.id_apply]
    refine congrArg₂ (· • ·) (hcarry u v) ((AddEquiv.symm_apply_eq _).2 ?_)
    exact (groundLevelEquiv_symm_apply_coe _ _ a').trans ha.symm
  · rw [explicitCor2_comp_res2, ground_ofOpenNormal, OpenSubgroup.toSubgroup_top,
      Subgroup.index_top, one_smul]

end Layer
end Idele
end TauCeti.ClassFieldTheory
end
end
