public section

namespace CFSG.RankThree.GF2n.Stroth80.Gl37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Glue

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem conj_LB_eq_of_fix_line (hc : Ctx M Q Z B) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {a : G} (haM : a ∈ M)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) {μ : K}
    (hTb : T b = μ • b) : conjSubgroup a (LB M Q B) = LB M Q B :=
  conj_LB_eq_of_maps_line hc hB haM hT fun s => ⟨s * μ, by rw [map_smul, hTb, smul_smul]⟩

end Glue
end CFSG.RankThree.GF2n.Stroth80.Gl37
end
