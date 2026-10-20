namespace P2MW.S_Algebra_PatchingDatum_nonempty_patchingLevel_bot

section PCPortSpine1

set_option autoImplicit false

variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]

variable [∀ i, Module (R i) (M i)]

variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i))

namespace LinearMap p2m_export "LinearMap" "coe_comp mem_range range coe_mk toAddMonoidHom inverse rank add_apply ker_eq_bot id_coe id sum_apply piMap range_eq_top_of_surjective module ker_comp_of_ker_eq_bot range_comp le_def addCommGroup map_span codRestrict inr neg_apply zero_apply smul_apply coe_restrictScalars fst ker_comp mk coe_coe id_apply pi mul proj ext range_eq_top compLeft_apply map_smul_of_tower comp single lsum restrictScalars ker continuous_on_pi quotKerEquivOfSurjective inl mem_ker comp_apply rank_le_of_surjective restrict instIsScalarTower pi_apply" end LinearMap

p2m_open_scoped "LinearMap" in

namespace TwoSidedIdeal p2m_export "TwoSidedIdeal" "matrix mul_mem_right ker_eq_bot ker span_le coe_mk comap mk subset_span neg_mem mul_mem_left mk' mem_iff addCommGroup op add_mem span asIdeal ext mem_iInf mem_span_iff mem_comap map unop mem_bot mem_top map_mono mem_sup_right mem_ker span_induction subtype zero_mem mem_sup" end TwoSidedIdeal

p2m_open_scoped "TwoSidedIdeal" in

p2m_reactivate

p2m_open_scoped "TwoSidedIdeal" in

p2m_reactivate

p2m_open_scoped "TwoSidedIdeal" in

p2m_reactivate

p2m_open_scoped "TwoSidedIdeal" in

p2m_open_scoped "TwoSidedIdeal" in

p2m_open_scoped "TwoSidedIdeal" in

p2m_open_scoped "TwoSidedIdeal" in

namespace WellFoundedGT p2m_export "WellFoundedGT" "apply induction" end WellFoundedGT

p2m_open_scoped "WellFoundedGT" in

namespace WellFoundedLT p2m_export "WellFoundedLT" "apply induction" end WellFoundedLT

p2m_open_scoped "WellFoundedLT" in

namespace IsLocalRing p2m_export "IsLocalRing" "ResidueField exists_maximalIdeal_pow_le_of_isArtinianRing_quotient map_maximalIdeal_le of_surjective maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal mem_maximalIdeal jacobson_eq_maximalIdeal of_injective local_hom_TFAE of_surjective' isOpen_maximalIdeal_pow map_maximalIdeal_of_surjective ResidueField.map residue" end IsLocalRing

p2m_open_scoped "IsLocalRing" in

namespace Submodule p2m_export "Submodule" "quotEquivOfEq le_of_le_smul_of_le_jacobson_bot Quotient.eq quotientRel_def finite_quotient_smul isCompact_of_fg Quotient.addCommGroup ker_liftQ factor mem_sup_right range_mkQ map_top smul_mem' mk smul_mem map_comap_eq mem_bot mapQ_id smul_le mapQ_apply Quotient.mk span restrictScalars smul_induction_on coe_restrictScalars toAddSubmonoid annihilator_top addCommGroup mem_map_of_mem add_mem_sup span_le continuousSMul_quotient mem_comap mem_span_range_iff_exists_fun fst toAddSubgroup map_smul'' mem_top mem_span_singleton mul_mem_mul smul_mem_smul mkQ mem_map mul mem_iInf generators nontrivial_iff map_mono fg_def map_smul' map_comp zero one map_span annihilator_eq_top_iff comap_map_eq mem_annihilator Quotient.mk_surjective map span_neg Quotient.nontrivial_iff Quotient.mk_smul coe_mk mem_sup annihilator map_id Quotient.mk_eq_zero comap_bot mkQ_surjective closure_eq matrix range_liftQ subset_span map_injective_of_injective mapQ instIsScalarTower module mk_eq_zero FG smul_mono mapQ_comp mkQ_apply pi sup_smul ext comap_top projection ker_mkQ add comap comap_mono map_sup span_induction liftQ coe_zero map_le_iff_le_comap smul" end Submodule

p2m_open_scoped "Submodule" in

p2m_open_scoped "Submodule" in

namespace Pi p2m_export "Pi" "single single_eq_of_ne monoid addCommGroup discreteTopology t2Space one_apply single_smul zero_apply ringHom_apply nontrivial group map_id map_apply add_apply ring finite module algebraMap_apply complete evalRingHom_apply mul_apply algebra evalRingHom le_def neg_apply compactSpace faithfulSMul smul_apply" end Pi

p2m_open_scoped "Pi" in

p2m_open_scoped "Pi" in

p2m_open_scoped "Pi" in

p2m_reactivate

p2m_reactivate

section PCPortSpine3

variable (R S) [CommRing R] [Ring S] [Algebra R S] [TopologicalSpace S]

namespace Algebra p2m_export "Algebra" "linearMap_apply FiniteType.out ofId map_sup map_top commutes mk algebraMap mem_top eq_top_iff mem_iInf comap_top compHom FiniteType toModule algebraMap_self_apply adjoin id ofModule mem_bot restrictScalars adjoin_induction commutes' mem_sup_right PatchingLevel PatchingDatum" end Algebra

p2m_open_scoped "Algebra" in

scoped instance (priority := 100) [IsTopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

variable {M} [AddCommGroup M] [Module R M] [TopologicalSpace M] [T2Space M]

p2m_reactivate

p2m_reactivate

section PCPortSpine5

variable (R₀ : Type*) [CommRing R₀]

variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]

variable [∀ i, Algebra R₀ (R i)] [∀ i, Module (R i) (M i)]

variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i)) (F : Filter ι)

open Filter

variable {F}

scoped instance : AddCommGroup (UltraProduct M F) := inferInstanceAs
  (AddCommGroup ((Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ ℤ) (M := M) ⊥ F))

scoped instance : CommRing (UltraProduct R F) := inferInstanceAs
  (CommRing ((Π i, R i) ⧸ eventuallyProd (R := R) (M := R) ⊥ F))

scoped instance : Module (Π i, R i) (UltraProduct M F) :=
  inferInstanceAs (Module (Π i, R i) ((Π i, M i) ⧸ eventuallyProd (R := R) (M := M) ⊥ F))

variable {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra (R i) (A i)]

variable {R₀} [∀ i, Module R₀ (M i)] [∀ i, IsScalarTower R₀ (R i) (M i)]

variable {M₀} [AddCommGroup M₀] [Module R₀ M₀]

scoped instance : Module R₀ (UltraProduct M F) :=
  inferInstanceAs (Module R₀ ((Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ R₀) (M := M) ⊥ F))

scoped instance : Algebra R₀ (UltraProduct R F) :=
  inferInstanceAs (Algebra R₀ ((Π i, R i) ⧸ eventuallyProd (R := R) (M := R) ⊥ F))

set_option backward.isDefEq.respectTransparency false in
scoped instance : IsScalarTower R₀ (Π i, R i) (UltraProduct M F) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  obtain ⟨m, rfl⟩ := UltraProduct.πₗ_surjective R m
  change _ = _ • Submodule.mkQ (eventuallyProd (R := fun _ ↦ R₀) (M := M) ⊥ F) m
  rw [← map_smul, ← LinearMap.map_smul_of_tower, algebraMap_smul]
  rfl

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

scoped instance : SMul (UltraProduct R F) (UltraProduct M F) where
  smul := Quotient.lift₂ (UltraProduct.πₗ R M F <| · • ·) fun r₁ m₁ r₂ m₂ e₁ e₂ ↦ by
    rw [← sub_eq_zero]
    simp only [← map_sub, UltraProduct.πₗ_eq_zero]
    filter_upwards [(Submodule.quotientRel_def _).mp e₁,
      (Submodule.quotientRel_def _).mp e₂] with i h₁ h₂
    simp_all [sub_eq_zero]

p2m_reactivate

scoped instance : Module (UltraProduct R F) (UltraProduct M F) :=
    Function.Surjective.moduleLeft (Ideal.Quotient.mk (eventuallyProd (R := R) (M := R) ⊥ F))
    UltraProduct.π_surjective fun _ _ ↦ UltraProduct.π_smul

set_option backward.isDefEq.respectTransparency false in
scoped instance : IsScalarTower R₀ (UltraProduct R F) (UltraProduct M F) := by
  constructor
  intros r s m
  obtain ⟨s, rfl⟩ := UltraProduct.π_surjective s
  rw [UltraProduct.π_smul, ← @IsScalarTower.algebraMap_smul R₀ (Π i, R i),
    ← UltraProduct.π_smul, smul_eq_mul, mul_smul, UltraProduct.π_smul,
    UltraProduct.π_smul, IsScalarTower.algebraMap_smul]

scoped instance : TopologicalSpace (UltraProduct M F) := ⊥

scoped instance : DiscreteTopology (UltraProduct M F) := ⟨rfl⟩

scoped instance : IsTopologicalAddGroup (UltraProduct M F) where

scoped instance : IsTopologicalRing (UltraProduct R F) where

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (R i) (N i)]

p2m_reactivate

p2m_reactivate

variable {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀] (f : ∀ i, M₀ →ₗ[R₀] M i)

lemma UltraProduct.exists_algEquiv_of_bddAbove_card
    [TopologicalSpace R₀]
    [IsTopologicalRing R₀]
    [Algebra.TopologicallyFG ℤ R₀]
    [∀ i, TopologicalSpace (R i)]
    [∀ i, T2Space (R i)] (F : Ultrafilter ι)
    (N : ℕ) (H : ∀ᶠ i in F, Finite (R i) ∧ Nat.card (R i) < N)
    (hcont : ∀ᶠ i in F, ContinuousSMul R₀ (R i)) :
    ∀ᶠ i in F, Nonempty (UltraProduct R F ≃ₐ[R₀] R i) := by
  classical
  have : ∀ᶠ i in F, ∃ (α : TopologicalAlgebraTypeCardLT R₀ N)
    (e : R i ≃ₐ[R₀] Fin α.1), IsHomeomorph e := by
    filter_upwards [H, hcont] with i ⟨h₁, h₂⟩ h₃
    exact ⟨_, TopologicalAlgebraTypeCardLT.equivOfAlgebra N _ h₂,
      TopologicalAlgebraTypeCardLT.isHomeomorph_equivOfAlgebra N _ h₂⟩
  obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp this
  let g (i) := if h : Nonempty (R i ≃ₐ[R₀] Fin a.1) then h.some.symm.toLinearMap else 0
  let e := LinearEquiv.ofBijective _
    (UltraProduct.bijective_of_eventually_bijective (R₀ := R₀) (M := R) (M₀ := Fin a.1) g F
    (by filter_upwards [ha] with i hi; unfold g;
        rw [dif_pos ⟨hi.choose⟩]; exact AlgEquiv.bijective _))
  let e' : Fin ↑a.fst ≃ₐ[R₀] UltraProduct R F := by
    refine AlgEquiv.ofLinearEquiv e ?_ ?_
    · rw [← (π R F).map_one]
      refine UltraProduct.πₗ_eq_iff.mpr ?_
      filter_upwards [ha] with i hi
      simp only [g, LinearMap.pi_apply, Pi.one_apply, dif_pos (Nonempty.intro (hi.choose)),
        AlgEquiv.toLinearMap_apply, map_one]
    · intro x y
      change _ = π R F _ * π R F _
      rw [← map_mul]
      refine UltraProduct.πₗ_eq_iff.mpr ?_
      filter_upwards [ha] with i hi
      simp only [LinearMap.pi_apply, dif_pos (Nonempty.intro (hi.choose)),
        AlgEquiv.toLinearMap_apply, map_mul, Pi.mul_apply, g]
  filter_upwards [ha] with i ⟨e, he⟩
  exact ⟨e'.symm.trans e.symm⟩

end PCPortSpine5
end Algebra
end PCPortSpine3
end Pi
end Submodule
end IsLocalRing
end WellFoundedLT
end WellFoundedGT
end TwoSidedIdeal
end LinearMap
end PCPortSpine1
end P2MW.S_Algebra_PatchingDatum_nonempty_patchingLevel_bot
