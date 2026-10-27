public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

open CFSG.QuasithinUnique.Setup.X7b

open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isNatural_of_twist {f : ℕ} (hf : 2 ≤ f) {L : Subgroup (GLV V)}
    (φ : ↥L ≃* antiSp (GaloisField 2 f)) (i : ℕ) (θ : V ≃+ (Fin 4 → GaloisField 2 f))
    (hθ : ∀ (g : antiSp (GaloisField 2 f)) (w : V), θ (piOf L φ g w) =
      (glMat (((minorAut (GaloisField 2 f) ^ i) g : antiSp (GaloisField 2 f)) :
        GL (Fin 4) (GaloisField 2 f))).mulVec (θ w)) :
    IsNaturalMatrixModule L ⁅CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f),
      CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : CharP (GaloisField 2 f) 2 := inferInstance
  have hperf := commutator_statedSp_eq h4
  let Φ : ↥L ≃* ↥⁅CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f),
      CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f)⁆ :=
    (((φ.trans (show antiSp (GaloisField 2 f) ≃* antiSp (GaloisField 2 f) from
      minorAut (GaloisField 2 f) ^ i)).trans
      (antiSpEquiv (GaloisField 2 f))).trans (MulEquiv.subgroupCongr hperf.symm))
  refine ⟨Φ, coordEquiv θ, fun h v => ?_⟩
  have hg := hθ (φ h) v
  rw [piOf_apply, MulEquiv.symm_apply_apply] at hg
  funext s
  rw [coordEquiv_apply, hg]
  have hmat : ((Φ h : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) =
      (glMat (((minorAut (GaloisField 2 f) ^ i) (φ h) : antiSp (GaloisField 2 f)) :
        GL (Fin 4) (GaloisField 2 f))).submatrix antiIdx antiIdx := rfl
  have hco : (coordEquiv θ v) ∘ antiIdx.symm = θ v := by
    funext c
    show θ v (antiIdx (antiIdx.symm c)) = θ v c
    rw [Equiv.apply_symm_apply]
  rw [hmat, Matrix.submatrix_mulVec_equiv, hco]
  rfl

end CFSG.Quasithin.G11.Harris.Sp4
end
