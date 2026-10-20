public section

namespace TauCeti

section Conjugation

namespace DiscreteCoind

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] {U V : Subgroup G}
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]

variable (U V M) in
/-- **Conjugation of coinduced modules.** For `g : G` and a subgroup `V ≤ gUg⁻¹`, the map
`Coind_U^G M → Coind_V^G M` sending `f` to `x ↦ g • f (g⁻¹ x)`. It is `G`-equivariant for the
right-translation actions, and for `V = gUg⁻¹` it commutes with the traces (`trace_conj`). -/
def conj (g : G) (hVU : V ≤ U.map (MulAut.conj g).toMonoidHom) :
    DiscreteCoind G U M →+[G] DiscreteCoind G V M where
  toFun f := mk G V M (fun x => g • f (g⁻¹ * x))
    ((f.isLocallyConstant.comp_continuous (continuous_const_mul g⁻¹)).comp (g • ·))
    fun v x => by
      -- `g⁻¹ (v x) = (g⁻¹ v g) (g⁻¹ x)` with `g⁻¹ v g ∈ U`, and `g (g⁻¹ v g) = v g`.
      have hv := Subgroup.mem_map_equiv.1 (hVU v.2)
      rw [MulAut.conj_symm_apply] at hv
      have hx : g⁻¹ * ((v : G) * x) = ((⟨g⁻¹ * v * g, hv⟩ : U) : G) * (g⁻¹ * x) := by
        simp [mul_assoc]
      rw [hx, apply_mul, Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul]
      simp [mul_assoc]
  map_zero' := ext fun x => by simp
  map_add' f f' := ext fun x => by simp
  map_smul' h f := ext fun x => by simp [mul_assoc]

end DiscreteCoind
end Conjugation
end TauCeti
end
