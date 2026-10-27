public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open CFSG.Open (StatedLieTag StatedLieAdmissible)

open CFSG.SeitzReduction.F4Pilot (suCongr coe_suCongr)

theorem irgUM_longRootHom_map_entrywise {F : Type} [Field F] {σ : F ≃+* F}
    (φ : F ≃+* F) (hφ : ∀ c, φ (σ c) = σ (φ c))
    {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    (longRootHom σ hi).range.map
        (suCongr φ hφ n).toMonoidHom =
      (longRootHom σ hi).range := by
  have hφ' : ∀ c, φ.symm (σ c) = σ (φ.symm c) := fun c => by
    apply φ.injective
    rw [φ.apply_symm_apply, hφ, φ.apply_symm_apply]
  have hle : (longRootHom σ hi).range.map
      (suCongr φ hφ n).toMonoidHom ≤
      (longRootHom σ hi).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd
      ⟨φ (z.toAdd : F), irgU_traceZero_preserved σ φ hφ z.toAdd.2⟩, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom]
    apply Units.ext
    ext p q
    rw [coe_suCongr, Unitary.coe_longRootHom, Unitary.coe_longRootHom]
    simpa [Matrix.map_apply] using
      (congrFun (congrFun (irgU_map_longRootMatrix (F := F) (n := n) φ i (z.toAdd : F)) p) q).symm
  have hle' : (longRootHom σ hi).range.map
      (suCongr φ.symm hφ' n).toMonoidHom ≤
      (longRootHom σ hi).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd
      ⟨φ.symm (z.toAdd : F), irgU_traceZero_preserved σ φ.symm hφ' z.toAdd.2⟩, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom]
    apply Units.ext
    ext p q
    rw [coe_suCongr, Unitary.coe_longRootHom, Unitary.coe_longRootHom]
    simpa [Matrix.map_apply] using
      (congrFun (congrFun
        (irgU_map_longRootMatrix (F := F) (n := n) φ.symm i (z.toAdd : F)) p) q).symm
  apply le_antisymm hle
  intro x hx
  have hx' : (suCongr φ.symm hφ' n) x ∈
      (longRootHom σ hi).range :=
    hle' (Subgroup.mem_map_of_mem _ hx)
  have hx'' : (suCongr φ hφ n)
      ((suCongr φ.symm hφ' n) x) ∈
      (longRootHom σ hi).range.map
        (suCongr φ hφ n).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx'
  have hs : (suCongr φ hφ n) ((suCongr φ.symm hφ' n) x) = x := by
    apply Subtype.ext
    apply Units.ext
    ext p q
    simp [coe_suCongr]
  rwa [hs] at hx''

end CFSG.StandardType.RCKRP
end
