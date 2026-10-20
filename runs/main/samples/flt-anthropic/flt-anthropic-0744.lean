namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle

set_option autoImplicit false

open scoped MatrixGroups

open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

p2m_reactivate

open CycleUnitCoords in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀]
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {G : Type} [Group G]
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})

    (η : G →* Kˣ) (hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1) (hη : ∀ γ : G, IsOfFinOrder γ → η γ = 1) :
    ∃ ζ : E → Kˣ, (∀ e : E, Valued.v ((ζ e : Kˣ) : K) = 1) ∧
      ∀ β : G, ((η β : Kˣ) : K) = ∏ e : E, ((ζ e : Kˣ) : K) ^
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) β e := by
  classical
  have hT := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  let V := CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀)
  let D : CerednikDrinfeld.DegeneracyData E V :=
    ⟨fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
     fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd, fun _ => 1⟩
  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V) (fun _ => rfl) (fun _ => rfl)
    (LT.LatticeTree.stdVertex R K₀)
  have hdiv : ∀ (a : ↥(unitSphere K)) (n : ℕ), n ≠ 0 → ∃ b : ↥(unitSphere K), b ^ n = a :=
    fun a n hn => exists_pow_eq a n (Nat.pos_of_ne_zero hn)
  have hηU : ∀ g : G, η g ∈ unitSphere K := fun g => hη₁ g
  let c : G →* ↥(unitSphere K) := η.codRestrict (unitSphere K) hηU
  have hc : ∀ (w : LT.LatticeTree.Vertex R K₀) (g : G), g ∈ MulAction.stabilizer G w → c g = 1 := by
    intro w g hg
    haveI := hfin w
    have hfo : IsOfFinOrder g :=
      (MulAction.stabilizer G w).subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨g, hg⟩ : ↥(MulAction.stabilizer G w)))
    apply Subtype.ext
    show ((η g : Kˣ)) = ((1 : ↥(unitSphere K)) : Kˣ)
    rw [hη g hfo, OneMemClass.coe_one]
  obtain ⟨ν, hν⟩ := CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V) (fun _ => rfl) (fun _ => rfl)
    (LT.LatticeTree.stdVertex R K₀) Φ hΦ ↥(unitSphere K) hdiv c hc
  refine ⟨fun e => ((ν e : ↥(unitSphere K)) : Kˣ), fun e => (ν e).2, fun β => ?_⟩
  have h := hν β
  rw [hΦ β] at h
  have h2 := congrArg (fun u : ↥(unitSphere K) => ((u : Kˣ) : K)) h
  simp only [Subgroup.val_finset_prod, SubgroupClass.coe_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val] at h2
  exact h2

end P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
