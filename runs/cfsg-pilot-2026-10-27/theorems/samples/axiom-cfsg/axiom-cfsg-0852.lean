public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

variable {G : Type*} [Group G]

section Control

variable {M : Subgroup G} {d : G}

theorem existsUnique_fixed_coset (hdM : d ∈ M)
    (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ dZero M d) {a : G} (ha : IsConj d a) :
    ∃! q : G ⧸ M, a • q = q := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ha
  refine ⟨(g : G ⧸ M), smul_coe_eq_self_iff_conj_mem.2 ?_, fun q hq => ?_⟩
  · have e : g⁻¹ * a * g = d := by rw [← hg]; group
    rw [e]
    exact hdM
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx := smul_coe_eq_self_iff_conj_mem.1 hq
    have hD : x⁻¹ * a * x ∈ dZero M d :=
      hDM _ hx (ha.trans (isConj_iff.2 ⟨x⁻¹, by group⟩))
    have e : x⁻¹ * g * d * (x⁻¹ * g)⁻¹ = x⁻¹ * a * x := by rw [← hg]; group
    exact QuotientGroup.eq.2 (mem_of_conj_mem_dZero hC (self_mem_dZero M d) (e ▸ hD))

end Control
end CFSG.Monster.B.GSide
end
