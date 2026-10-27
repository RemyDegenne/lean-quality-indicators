public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open scoped commutatorElement

namespace S8

namespace L89

variable {G : Type} [Group G] [Finite G]

section Setup

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem Ta_inf_centralizer_D (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) :
    cfgT c.R M ⊓ cx a ⊓ Subgroup.centralizer (c.D : Set G) = cfgR0 c.R c.D := by
  rw [inf_assoc, inf_eq_right.2 (centralizer_le_cx_of_mem ha), T_inf_centralizer_D c hNM]

end Setup
end L89
end S8
end CFSG.LocalAnalysis.GLTheoremA
end
