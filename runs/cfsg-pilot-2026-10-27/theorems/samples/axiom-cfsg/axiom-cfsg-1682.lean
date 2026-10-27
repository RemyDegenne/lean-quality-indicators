public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

namespace ThirdKindHyp

variable {S : Sylow 2 G} {a b c : G} {n : ℕ} (h : ThirdKindHyp G D S a b c n)

include h

theorem z_mem_pCore : (a * c * b) ^ n ∈ CFSG.pCore 2 G := by
  obtain ⟨hzz, -⟩ := h.z_spec
  have hle : Subgroup.zpowers ((a * c * b) ^ n) ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr h.z_mem_center
  have hn : (Subgroup.zpowers ((a * c * b) ^ n)).Normal := Subgroup.normal_of_le_center hle
  have h2 : IsPGroup 2 (Subgroup.zpowers ((a * c * b) ^ n)) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases (mem_zpowers_of_mul_self hzz).mp hg with rfl | rfl
    · simp
    · simp [pow_two, hzz]
  have hle2 : Subgroup.zpowers ((a * c * b) ^ n) ≤ CFSG.pCore 2 G := le_sSup ⟨hn, h2⟩
  exact hle2 (Subgroup.mem_zpowers _)

end ThirdKindHyp
end CFSG.Timmesfeld.Bridge
end
