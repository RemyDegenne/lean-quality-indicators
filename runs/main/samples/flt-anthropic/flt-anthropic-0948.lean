namespace P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

p2m_open

namespace P2MToricLevel

universe u v

section Toric

variable (K : Type u) [Field K] {ζ : K}

theorem relations_K_two (hζ0 : ζ ≠ 0) {a b : ℕ} (ha : ζ ^ a ≠ 1) (hb : ζ ^ b ≠ 1)
    (hab : ζ ^ (a + b) ≠ 1) :
    ((toricPoint K 1 (ζ ^ a)).1 ≠ (toricPoint K 1 (ζ ^ b)).1 →
      chordRel (tateLaurent K) (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2
        (toricPoint K 1 (ζ ^ b)).1 (toricPoint K 1 (ζ ^ b)).2
        (toricPoint K 1 (ζ ^ (a + b))).1 (toricPoint K 1 (ζ ^ (a + b))).2) ∧
    (a = b →
      dblRel (tateLaurent K) (toricPoint K 1 (ζ ^ a)).1 (toricPoint K 1 (ζ ^ a)).2
        (toricPoint K 1 (ζ ^ (a + b))).1 (toricPoint K 1 (ζ ^ (a + b))).2) := by
  let σL : LaurentSeries (Rz K ζ) →+* LaurentSeries K := coeffMap (spec K ζ)
  have hW : (tateLaurent (Rz K ζ)).map σL = tateLaurent K := tateLaurent_map (spec K ζ)
  have hcd : cX K hζ0 a * cX K hζ0 b = cX K hζ0 (a + b) := cX_mul K hζ0 a b
  have h1c := isUnit_one_sub_cX K hζ0 ha
  have h1d := isUnit_one_sub_cX K hζ0 hb
  have h1cd : IsUnit (1 - ((cX K hζ0 a * cX K hζ0 b : (Rz K ζ)ˣ) : Rz K ζ)) := by
    rw [hcd]; exact isUnit_one_sub_cX K hζ0 hab
  have hc1 := cX_ne_one K hζ0 ha
  have hd1 := cX_ne_one K hζ0 hb
  have hcd1 : ((cX K hζ0 a * cX K hζ0 b : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
    rw [hcd]; exact cX_ne_one K hζ0 hab
  obtain ⟨hchord, hdbl⟩ := relations_R_two K (cX K hζ0 a) (cX K hζ0 b) h1c h1d h1cd hc1 hd1 hcd1

  have hxa : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1 = (toricPoint K 1 (ζ ^ a)).1 :=
    coeffMap_spec_toric_fst K hζ0 ha
  have hya : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).2 = (toricPoint K 1 (ζ ^ a)).2 :=
    coeffMap_spec_toric_snd K hζ0 ha
  have hxb : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).1 = (toricPoint K 1 (ζ ^ b)).1 :=
    coeffMap_spec_toric_fst K hζ0 hb
  have hyb : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).2 = (toricPoint K 1 (ζ ^ b)).2 :=
    coeffMap_spec_toric_snd K hζ0 hb
  have hxab : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a * cX K hζ0 b)).1
      = (toricPoint K 1 (ζ ^ (a + b))).1 := by
    rw [hcd]; exact coeffMap_spec_toric_fst K hζ0 hab
  have hyab : σL (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a * cX K hζ0 b)).2
      = (toricPoint K 1 (ζ ^ (a + b))).2 := by
    rw [hcd]; exact coeffMap_spec_toric_snd K hζ0 hab
  refine ⟨?_, ?_⟩
  · intro hxne
    have hxneR : (tateToricPoint (Rz K ζ) 1 (cX K hζ0 a)).1
        ≠ (tateToricPoint (Rz K ζ) 1 (cX K hζ0 b)).1 := by
      intro h; apply hxne; rw [← hxa, ← hxb, h]
    have h := chordRel_map σL _ (hchord hxneR)
    rw [hW, hxa, hya, hxb, hyb, hxab, hyab] at h
    exact h
  · intro habeq
    subst habeq
    have h := dblRel_map σL _ (hdbl rfl)
    rw [hW, hxa, hya, hxab, hyab] at h
    exact h

end Toric
end P2MToricLevel
end ModularCurve
end
end P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
