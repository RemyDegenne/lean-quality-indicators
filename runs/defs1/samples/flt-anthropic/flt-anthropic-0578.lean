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

p2m_reactivate

section PCPortSpine6

p2m_reactivate

section PCPortSpine7

set_option backward.isDefEq.respectTransparency false

variable (Λ : Type*) {ι : Type*} [CommRing Λ] (R : ι → Type*)

variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]

variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]

variable [∀ i, CompactSpace (R i)] [∀ i, IsLocalRing.IsAdicTopology (R i)]

variable (F : Ultrafilter ι)

variable [TopologicalSpace Λ] [IsTopologicalRing Λ] [∀ i, ContinuousSMul Λ (R i)]

variable [Algebra.TopologicallyFG ℤ Λ]

p2m_open

variable [Algebra.UniformlyBoundedRank R]

scoped instance (k) : T2Space (PatchingAlgebra.Component R F k) := DiscreteTopology.toT2Space

scoped instance (k : ℕ) : Finite (PatchingAlgebra.Component R F k) :=
  (PatchingAlgebra.componentEquiv ℤ R F k).exists.choose_spec.some.finite_iff.mpr
    (AddSubgroup.quotient_finite_of_isOpen _ (isOpen_maximalIdeal_pow'' _ _))

scoped instance : CommRing (PatchingAlgebra R F) :=
  inferInstanceAs (CommRing (PatchingAlgebra.subring R F))

scoped instance : Algebra Λ (PatchingAlgebra R F) :=
  inferInstanceAs (Algebra Λ (PatchingAlgebra.subalgebra Λ R F))

scoped instance : TopologicalSpace (PatchingAlgebra R F) :=
  inferInstanceAs (TopologicalSpace (PatchingAlgebra.subring R F))

scoped instance : T2Space (PatchingAlgebra R F) :=
  (Topology.IsEmbedding.subtypeVal).t2Space

variable {Rₒₒ} [CommRing Rₒₒ] (f : ∀ i, Rₒₒ →+* R i) [TopologicalSpace Rₒₒ]

variable [IsTopologicalRing Rₒₒ] [Algebra.TopologicallyFG ℤ Rₒₒ]

variable (hf : ∀ i, Continuous (f i))

variable [CompactSpace Rₒₒ]

p2m_reactivate

p2m_reactivate

section PCPortSpine8

local notation "Ann" => Module.annihilator

attribute [local instance] Module.quotientAnnihilator

section

p2m_open

variable {ι : Type*} (R : Type*) (M : ι → Type*) [CommRing R]

variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (F : Ultrafilter ι)

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

noncomputable section

namespace FrobDictPC

section Coeff

variable (𝒪 : Type) [CommRing 𝒪] (r : ℕ)

def Coeff : Type := MvPowerSeries (Fin r) 𝒪

end Coeff
end FrobDictPC
end
end
end PCPortSpine8
end PCPortSpine7
end PCPortSpine6
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
