namespace P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung

attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite HopfAlgebra.IsHopfTower.refl

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

open OrdSp in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {h : ℕ} (H : PDivisibleGroup O p h)

    (u ε w : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hu : ∀ v : ℕ, (H.transition v).comp (u (v + 1)) = (u v).comp (H.transition v))
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (H.transition v).comp (w (v + 1)) = (w v).comp (H.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    (hFV : ∀ Fk : ZMod p ⊗[O] H.level 1 →ₐc[ZMod p] ZMod p ⊗[O] H.level 1, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐ[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1), (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐc[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)),
        (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u 1)) :
            CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)))).ofConv)
    :
    ∀ (v : ℕ) (Cv : Type) [CommRing Cv] [HopfAlgebra (ZMod p) Cv] [Coalgebra.IsCocomm (ZMod p) Cv]
      [Module.Finite (ZMod p) Cv] [Module.Free (ZMod p) Cv]
      (q : ZMod p ⊗[O] H.level v →ₐc[ZMod p] Cv) (i : Cv →ₐc[ZMod p] ZMod p ⊗[O] H.level v),
      Function.Surjective q → q.comp i = BialgHom.id (ZMod p) Cv →
      i.comp q = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v) →
      ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : Cv →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) := by
  intro v Cv _ _ _ _ _ q i hq hqi hiq
  classical

  obtain ⟨hs, hrank, hker⟩ := PDivisibleGroup.surjective_and_finrank_and_ker_tensorProduct_map_transition p H (ZMod p)

  have heb : ∀ n : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n) := fun n => by rw [bc_comp, hεε]
  have het : ∀ n : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε (n + 1))) =
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)) := fun n => by
    rw [bc_comp, bc_comp, hεtr]

  have hOF1 := fun n : ℕ => HopfAlgebra.exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing (ZMod p) (ZMod p ⊗[O] H.level n)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) (heb n)
  choose C iC iH iCo iFin iFree qn inn hqn hqin hinq using hOF1
  letI : ∀ n, CommRing (C n) := iC
  letI : ∀ n, HopfAlgebra (ZMod p) (C n) := iH
  haveI : ∀ n, Coalgebra.IsCocomm (ZMod p) (C n) := iCo
  haveI : ∀ n, Module.Finite (ZMod p) (C n) := iFin
  haveI : ∀ n, Module.Free (ZMod p) (C n) := iFree

  obtain ⟨hT1, ⟨h₁, hh₁, hrankC⟩, hT3⟩ := PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
    p h (fun n => ZMod p ⊗[O] H.level n) (fun n => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n))
    hs hrank hker (fun n => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) heb het C qn inn hqn hqin hinq

  have hrel := fun (a b : H.level 1 →ₐc[O] H.level 1) => bc_comp (ZMod p) a b
  have hidFV := HopfAlgebra.exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
    p (ZMod p ⊗[O] H.level 1)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u 1))
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε 1))
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (w 1))
    (heb 1) (by rw [hrel, hrel, hεu]) (by rw [hrel, hεw]) (by rw [hrel, hwε]) (by rw [hrel, hrel, hwuε])
    (by rw [hrel, hrel, huεw]) hFV (C 1) (qn 1) (inn 1) (hqn 1) (hqin 1) (hinq 1)
  obtain ⟨C', _, _, _, _, _, q', i', hq', hq'i', hi'q', M₁, _, _, _, _, E₁, _, _, Θ₁, hΘ₁, hE₁, hM₁⟩ :=
    HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung p (C 1) (BialgHom.id (ZMod p) (C 1)) (by rfl) hidFV
  have hq'bij : Function.Bijective q' := by
    refine Function.bijective_iff_has_inverse.mpr ⟨i', fun x => ?_, fun y => ?_⟩
    · exact DFunLike.congr_fun hi'q' x
    · exact DFunLike.congr_fun hq'i' y
  have hord₁ : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
      (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
      (Θ : C 1 →ₐc[ZMod p] M ⊗[ZMod p] E),
      Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) :=
    ⟨M₁, inferInstance, inferInstance, inferInstance, inferInstance, E₁, inferInstance, inferInstance, Θ₁.comp q',
      hΘ₁.comp hq'bij, hE₁, hM₁⟩

  obtain ⟨M, _, _, _, _, E, _, _, Θv, hΘv, hE, hM⟩ := PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
    p h₁ C (fun n => (qn n).comp ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)).comp (inn (n + 1))))
    hT1 hrankC hT3 hord₁ v

  have hbij : Function.Bijective ((qn v).comp i) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨q.comp (inn v), fun x => ?_, fun y => ?_⟩
    · show q (inn v (qn v (i x))) = x
      have h1 : inn v (qn v (i x)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (i x) :=
        DFunLike.congr_fun (hinq v) (i x)
      rw [h1, ← hiq]
      show q (i (q (i x))) = x
      have h2 := DFunLike.congr_fun hqi
      simp only [BialgHom.comp_apply, BialgHom.id_apply] at h2
      rw [h2, h2]
    · show qn v (i (q (inn v y))) = y
      have h1 : i (q (inn v y)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (inn v y) := by
        rw [← hiq]; rfl
      rw [h1, ← hinq v]
      show qn v (inn v (qn v (inn v y))) = y
      have h2 := DFunLike.congr_fun (hqin v)
      simp only [BialgHom.comp_apply, BialgHom.id_apply] at h2
      rw [h2, h2]
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, E, inferInstance, inferInstance, Θv.comp ((qn v).comp i),
    hΘv.comp hbij, hE, hM⟩

end P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
