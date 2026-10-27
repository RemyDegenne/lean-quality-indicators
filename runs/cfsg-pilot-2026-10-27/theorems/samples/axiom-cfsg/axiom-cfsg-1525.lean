public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P512

variable {F : FanTree Γ G} (h510 : Fan510 F) (h511 : Fan511 F) (h40 : Fan40 F)

include h510 h511 h40

theorem no_long_core {T : Track Γ G} (hT : InXi T) {u : G} (hu : u ∈ T.line.ZZ) (hu1 : u ≠ 1)
    {a : ℤ} (h0 : u ∈ Cen (T.line.edgeStab (G := G) a : Set G))
    (h1 : u ∈ Cen (T.line.edgeStab (G := G) (a + 1) : Set G))
    (h2 : u ∈ Cen (T.line.edgeStab (G := G) (a + 2) : Set G)) : False := by
  obtain ⟨⟨a', b', tL, tR, hf⟩, huniv⟩ := coreSat2 h510 h511 h40 hT hu hu1
  have hP : ∀ k, u ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx u ∧ k + 1 ∈ T.line.fixIdx u := fun k hk => fix_of_cen hk
  obtain ⟨A, B, hA, hB, hcA⟩ := P514.exists_isCoreWith T.line hf.fix hP h1
  have hAa : A ≤ a := by
    by_contra hlt
    have hAe : A = a + 1 := by omega
    apply hcA.2.2.2.1
    rw [hAe, show a + 1 - 1 = a by ring]
    exact ⟨(fix_of_cen h0).1, h0⟩
  have hBa : a + 3 ≤ B := by
    by_contra hlt
    have hBe : B = a + 2 := by omega
    apply hcA.2.2.2.2
    rw [hBe]
    exact ⟨(fix_of_cen h2).1, h2⟩
  have := (huniv A B tL tR ⟨hf.fix, hcA⟩).1
  omega

end P512
end CFSG.Quasithin.Fan86
end
