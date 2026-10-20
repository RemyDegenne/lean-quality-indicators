namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

p2m_reactivate

open GlueFromBasisSol in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

    (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1)

    (M : ↥B → Type u) [∀ W, AddCommGroup (M W)] [∀ W, Module R (M W)] [∀ W, Module Γ(V, W.1.1) (M W)]
    [∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1; IsScalarTower R Γ(V, W.1.1) (M W)]
    (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[R] M W'))
    (res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(V, W.1.1)) (x : M W),
      res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x)
    (res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
    (res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
      res (h.trans h') x = res h (res h' x))
    (hqc : ∀ (W Wg : ↥B) (g : Γ(V, W.1.1)) (hWg : Wg.1.1 = V.basicOpen g),
      (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
          res (hWg.trans_le (V.basicOpen_le g)) x =
            (V.presheaf.map (homOfLE (hWg.trans_le (V.basicOpen_le g))).op).hom (g ^ n) • y) ∧
      (∀ x : M W, res (hWg.trans_le (V.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ W : ↥B, Module.Finite (Γ(V, W.1.1) : Type u) (M W)) :
    ∃ (G : OModulePresheaf π) (e : ∀ W : ↥B, G.obj W.1.1 ≃ₗ[R] M W),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : G.obj W.1.1), e W (a • x) = a • e W x) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : G.obj W.1.1), e W' (G.res h x) = res h (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (θ : ∀ W : ↥B, M W →ₗ[R] F.obj W.1.1),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : M W), θ W (a • x) = a • θ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θ W' (res h x) = F.res h (θ W x)) →
          ∃! Φ : OModulePresheaf.AffHom G F, ∀ (W : ↥B) (x : G.obj W.1.1), Φ.app W.1 x = θ W (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] M W),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = res h (ϑ W x)) →
          ∃! Ψ : OModulePresheaf.AffHom F G, ∀ (W : ↥B) (x : F.obj W.1.1), e W (Ψ.app W.1 x) = ϑ W x) := by
  let D : GlueFromBasisSol.GData π B :=
    { hdown := hdown, hcov := hcov, M := M, res := res, res_smul := res_smul, res_refl := res_refl,
      res_comp := res_comp, hqc := hqc, hfg := hfg }
  exact ⟨D.G, D.e, D.G_isCoherent, D.G_isQuasicoherent, D.e_smul, D.e_res,
    fun F hF θ hs hn => D.existsUnique_out hF θ hs hn, fun F _ ϑ hs hn => D.existsUnique_in ϑ hs hn⟩

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
