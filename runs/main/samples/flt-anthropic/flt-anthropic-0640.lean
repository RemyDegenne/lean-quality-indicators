namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq

set_option autoImplicit false

open scoped TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace X2Body

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section Local

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}

variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

theorem map_smulInto_line_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    (d.line (Mpi (K := K) hπ M')).map ((smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B) = d.line M' := by
  have hfac := smulInto_baseChange_eq (M := Mpi (K := K) hπ M') (M' := M') (B := B) hπ (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle1 : (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 ≤ M'.1 :=
    act_piUnit_le hπ (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle2 : M'.1 ≤ (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 := by
    intro v hv
    refine mem_latticeMap_scalarGL.mpr ⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • v,
      mem_latticeMap_scalarGL.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  apply le_antisymm
  · rw [hfac, Submodule.map_comp, ← d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M')]
    exact d.mono hle1
  ·
    have hround : (inclBaseChange B hle1) ∘ₗ (inclBaseChange B hle2) = LinearMap.id := by
      refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
      rw [LinearMap.comp_apply, inclBaseChange, inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.id_apply]
      rfl
    calc d.line M' = ((d.line M').map (inclBaseChange B hle2)).map (inclBaseChange B hle1) := by
          rw [← Submodule.map_comp, hround, Submodule.map_id]
      _ ≤ (d.line (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M'))).map (inclBaseChange B hle1) :=
          Submodule.map_mono (d.mono hle2)
      _ = _ := by rw [d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M'), ← Submodule.map_comp, ← hfac]

end Local
end X2Body
end P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
