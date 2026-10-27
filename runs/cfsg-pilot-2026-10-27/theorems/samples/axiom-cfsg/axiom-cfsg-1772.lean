public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra

open CFSG.Semidihedral.ElementaryActionTransport

open Module

theorem s16k_z3_model {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {Lb : Subgroup (MulAut W)} (hLb : IsCyclicOrd ↥Lb 3)
    (hfpf : ∀ l ∈ Lb, ∀ x : W, l x = x → l = 1 ∨ x = 1) :
    ∃ (e : W ≃* Multiplicative (Fin 6 → ZMod 2)) (φ : MulAut W ≃* S16kGL6),
      (∀ (g : MulAut W) (w : W), Multiplicative.toAdd (e (g w)) =
        ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd (e w))) ∧
      Lb.map φ.toMonoidHom = s16kScal := by
  classical
  haveI hEA : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hW }
  let V := Additive W
  haveI : Finite V := inferInstance
  have hfin6 : Module.finrank (ZMod 2) V = 6 := by
    have h := card_eq_prime_pow_finrank (p := 2) (R := W)
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) h).symm
  obtain ⟨ω₀, hω₀gen⟩ := hLb.1.exists_generator
  let ω : MulAut W := (ω₀ : MulAut W)
  have hωmem : ω ∈ Lb := ω₀.property
  have hLb_eq : Lb = Subgroup.zpowers ω := by
    apply le_antisymm
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥Lb) ∈ Subgroup.zpowers ω₀ := hω₀gen ⟨x, hx⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    · rw [Subgroup.zpowers_le]
      exact hωmem
  have hωorder : orderOf ω = 3 := by
    have h1 : orderOf (ω₀ : MulAut W) = orderOf ω₀ := Subgroup.orderOf_coe ω₀
    have h2 : orderOf ω₀ = 3 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hω₀gen, hLb.2]
    exact h1.trans h2
  have hωne : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωorder
    omega
  let z : LinearMap.GeneralLinearGroup (ZMod 2) V := autEquivGL (p := 2) (R := W) ω
  have hzorder : orderOf z = 3 := by
    have h1 : orderOf (autEquivGL (p := 2) (R := W) ω) = orderOf ω :=
      orderOf_injective (autEquivGL (p := 2) (R := W)).toMonoidHom
        (autEquivGL (p := 2) (R := W)).injective ω
    exact h1.trans hωorder
  have hzfix : ∀ v : V, (z : V →ₗ[ZMod 2] V) v = v → v = 0 := by
    intro v hv
    have hv' : (autEquivGL (p := 2) (R := W) ω : Module.End (ZMod 2) V)
        (Additive.ofMul (Additive.toMul v)) = Additive.ofMul (Additive.toMul v) := hv
    change (autToGL (p := 2) (R := W) ω : Module.End (ZMod 2) V)
        (Additive.ofMul (Additive.toMul v)) = Additive.ofMul (Additive.toMul v) at hv'
    rw [autToGL_apply] at hv'
    have hww : ω (Additive.toMul v) = Additive.toMul v := Additive.ofMul.injective hv'
    rcases hfpf ω hωmem (Additive.toMul v) hww with h1 | h1
    · exact absurd h1 hωne
    · have hv0 : v = 0 := by
        change (Additive.ofMul (Additive.toMul v) : Additive W) = 0
        rw [h1]
        rfl
      exact hv0
  letI : Module OmegaField V := omegaModule z hzorder hzfix
  haveI : IsScalarTower (ZMod 2) OmegaField V := omegaModule_isScalarTower z hzorder hzfix
  have homega : ∀ v : V, CFSG.LinearAlgebra.omega • v = (z : V →ₗ[ZMod 2] V) v :=
    omegaModule_omega_smul z hzorder hzfix
  have hfin3 : Module.finrank OmegaField V = 3 := by
    have hmul := Module.finrank_mul_finrank (ZMod 2) OmegaField V
    rw [finrank_omegaField, hfin6] at hmul
    omega
  let b3 : Basis (Fin 3) OmegaField V := finBasisOfFinrankEq OmegaField V hfin3
  let eLin : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) := s16k_coordEquiv b3
  let bF2 : Fin 6 → V := fun n => eLin.symm (Pi.single n 1)
  have hb3_even : ∀ i : Fin 3, bF2 (s16k_even i) = b3 i := by
    intro i
    change eLin.symm (Pi.single (s16k_even i) 1) = b3 i
    rw [← s16k_coordEquiv_basis b3 i, LinearEquiv.symm_apply_apply]
  have hb3_odd : ∀ i : Fin 3, bF2 (s16k_odd i) = CFSG.LinearAlgebra.omega • b3 i := by
    intro i
    change eLin.symm (Pi.single (s16k_odd i) 1) = CFSG.LinearAlgebra.omega • b3 i
    rw [← s16k_coordEquiv_omega_basis b3 i, LinearEquiv.symm_apply_apply]
  have hconj : (LinearMap.GeneralLinearGroup.congrLinearEquiv eLin
        (autEquivGL (p := 2) (R := W) ω) :
      (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      Matrix.mulVecLin (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro n
    rw [Pi.basisFun_apply]
    change eLin ((autEquivGL (p := 2) (R := W) ω : Module.End (ZMod 2) V) (bF2 n)) =
      Matrix.mulVecLin (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) (Pi.single n 1)
    rw [← homega (bF2 n)]
    rcases s16k_fin6_cases n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [hb3_even i, s16k_coordEquiv_omega_basis, Matrix.mulVecLin_apply,
        Matrix.mulVec_single_one, s16k_blockMat_prod, s16k_diagR_col_even]
    · rw [hb3_odd i, smul_smul, ← pow_two, omega_sq, add_smul, one_smul, map_add,
        s16k_coordEquiv_omega_basis, s16k_coordEquiv_basis, Matrix.mulVecLin_apply,
        Matrix.mulVec_single_one, s16k_blockMat_prod, s16k_diagR_col_odd]
  let e : W ≃* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (eLin (Additive.ofMul w))
      invFun := fun x => Additive.toMul (eLin.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp
      right_inv := fun x => by simp
      map_mul' := fun a b => by simp }
  let φ : MulAut W ≃* S16kGL6 :=
    (autEquivGL (p := 2) (R := W)).trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv eLin).trans
        (Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := ZMod 2)).symm)
  have htofun : ∀ g : MulAut W,
      Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := ZMod 2) (φ g) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv eLin (autEquivGL (p := 2) (R := W) g) := by
    intro g
    simp only [φ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e, φ, ?_, ?_⟩
  · intro g w
    have happ : (autEquivGL (p := 2) (R := W) g : Module.End (ZMod 2) V)
        (Additive.ofMul w) = Additive.ofMul (g w) := by
      change (autToGL (p := 2) (R := W) g : Module.End (ZMod 2) V) (Additive.ofMul w) =
        Additive.ofMul (g w)
      rw [autToGL_apply]
    have hc := s16k_congrLinearEquiv_apply eLin (autEquivGL (p := 2) (R := W) g)
      (eLin (Additive.ofMul w))
    rw [LinearEquiv.symm_apply_apply] at hc
    rw [happ] at hc
    change eLin (Additive.ofMul (g w)) =
      Matrix.mulVec ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (eLin (Additive.ofMul w))
    conv_rhs => rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, htofun g]
    exact hc.symm
  · have hφω : ((φ ω : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 := by
      apply Matrix.ext_of_mulVec_single
      intro n
      conv_lhs => rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, htofun ω,
        hconj]
      rw [Matrix.mulVecLin_apply]
    have hscal : s16kScal = Subgroup.zpowers (φ ω) := by
      rw [s16kScal, Subgroup.zpowers_eq_closure]
      congr 1
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hg
        exact Units.ext (hg.trans hφω.symm)
      · intro hg
        rw [hg]
        exact hφω
    calc Lb.map φ.toMonoidHom = (Subgroup.zpowers ω).map φ.toMonoidHom := by rw [hLb_eq]
      _ = Subgroup.zpowers (φ ω) := MonoidHom.map_zpowers φ.toMonoidHom ω
      _ = s16kScal := hscal.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
