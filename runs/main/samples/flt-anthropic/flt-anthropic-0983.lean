namespace P2MW.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper

set_option autoImplicit false

open Matrix MatrixGroups ModularCurve

namespace P2mDicksonBorel

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

section OrbitCount

variable {H : Type} [Group H] [Finite H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)

variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H} (D : NormData ρ P)

variable (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)

variable {b : Subgroup.normalizer (P : Set H)} (hb : (chi D b) ^ 2 ≠ 1)
  (hgen : ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range))

include hρ D in
omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma torus_smul_eq {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hbss : IsSS ρ (b : H)) {c : H} (hc : c ∈ torus (b : H)) : c • (n₀ • P) = n₀ • P := by
  have hc' : n₀⁻¹ * c * n₀ ∈ torus (b : H) := by
    rw [Subgroup.mem_normalizer_iff''] at hn₀
    exact (hn₀ c).mp hc
  have hB : n₀⁻¹ * c * n₀ ∈ Subgroup.normalizer (P : Set H) := torus_le_B hρ D b.2 hbss hc'
  rw [← Sylow.smul_eq_iff_mem_normalizer] at hB
  calc c • (n₀ • P) = n₀ • ((n₀⁻¹ * c * n₀) • P) := by
        rw [← mul_smul, ← mul_smul, show n₀ * (n₀⁻¹ * c * n₀) = c * n₀ by group]
    _ = n₀ • P := by rw [hB]

end OrbitCount
end P2mDicksonBorel
end P2MW.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper
