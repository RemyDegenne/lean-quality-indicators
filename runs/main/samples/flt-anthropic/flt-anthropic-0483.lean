namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ

set_option maxHeartbeats 4000000

set_option synthInstance.maxHeartbeats 400000

attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule

universe u

namespace StalkConstr

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule TensorProduct

section ZpExtension

variable {p : ℕ} [Fact p.Prime]

theorem padicInt_exists_nat_add (n : ℕ) (r : ℤ_[p]) : ∃ (k : ℕ) (r' : ℤ_[p]), r = k + (p : ℤ_[p]) ^ n * r' := by
  have hk : r - ((PadicInt.toZModPow n r).val : ℕ) ∈ RingHom.ker (PadicInt.toZModPow (p := p) n) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨r', hr'⟩ := hk
  exact ⟨(PadicInt.toZModPow n r).val, r', by rw [mul_comm, hr']; abel⟩

end ZpExtension
end StalkConstr
end P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ
