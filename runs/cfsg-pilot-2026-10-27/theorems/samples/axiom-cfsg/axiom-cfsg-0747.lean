public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

section Transport

variable {K K' : Type} [Group K] [Group K'] {p : ℕ}

variable [Finite K]

theorem AutFixInner.of_sylow (hp : p.Prime) {T₀ : Sylow p K} (D : AutFixInner p K T₀)
    (T : Sylow p K) : AutFixInner p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine AutFixInner.of_equiv (MulAut.conj g⁻¹) (T' := T₀) ?_ D
  have h1 : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact coe_smul_sylow_eq_map T₀ g
  rw [h1, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (T₀ : Subgroup K)]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.id_apply]
  group

end Transport
end CFSG.AGLEmbedding.KFactProofs.SmallIdent
end
