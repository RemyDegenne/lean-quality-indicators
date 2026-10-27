public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

open scoped commutatorElement

theorem ParabolicLeviData.map_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {U A P O : Subgroup G} {d₁ d₂ d₃ : ℕ}
    (h : ParabolicLeviData U A P O d₁ d₂ d₃) :
    ParabolicLeviData (U.map f) (A.map f) (P.map f) (O.map f) d₁ d₂ d₃ := by
  unfold ParabolicLeviData at h
  obtain ⟨hPU, hOP, hAO, hO2, hnorm, hnrm, hdisj⟩ := h
  refine ⟨Subgroup.map_mono hPU, Subgroup.map_mono hOP, Subgroup.map_mono hAO,
    hO2.map f, ?_, ?_, ?_⟩
  · intro p hp o ho
    obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨o₀, ho₀, rfl⟩ := Subgroup.mem_map.mp ho
    exact Subgroup.mem_map.mpr ⟨p₀ * o₀ * p₀⁻¹, hnorm p₀ hp₀ o₀ ho₀, by simp⟩
  · intro g hg hgn
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
    refine Subgroup.mem_map.mpr ⟨g₀, hnrm g₀ hg₀ ?_, rfl⟩
    intro a ha
    exact (Subgroup.mem_map_iff_mem hf).1
      (by simpa using hgn (f a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
  · intro S hSP hSperf
    have hSrange : S ≤ f.range := hSP.trans (Subgroup.map_le_range f P)
    have hmapS : (S.comap f).map f = S := Subgroup.map_comap_eq_self hSrange
    have hS₀P : S.comap f ≤ P := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hSP
    have eS : ↥S ≃* ↥(S.comap f) :=
      (MulEquiv.subgroupCongr hmapS).symm.trans
        (Subgroup.equivMapOfInjective (S.comap f) f hf).symm
    have hS₀perf : commutator ↥(S.comap f) = ⊤ := by
      haveI : Group.IsPerfect ↥S := Group.IsPerfect.mk hSperf
      haveI : Group.IsPerfect ↥(S.comap f) :=
        Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective
      exact Group.IsPerfect.commutator_eq_top
    have hcardS : Nat.card ↥(S.comap f) = Nat.card ↥S := by
      calc Nat.card ↥(S.comap f)
          = Nat.card ↥((S.comap f).map f) := (Subgroup.card_map_of_injective hf).symm
        _ = Nat.card ↥S := Nat.card_congr (MulEquiv.subgroupCongr hmapS).toEquiv
    have hmapSO : (S.comap f ⊓ O).map f = S ⊓ O.map f := by
      rw [Subgroup.map_inf (S.comap f) O f hf, hmapS]
    have hcardSO : Nat.card ↥(S.comap f ⊓ O) = Nat.card ↥(S ⊓ O.map f) := by
      calc Nat.card ↥(S.comap f ⊓ O)
          = Nat.card ↥((S.comap f ⊓ O).map f) := (Subgroup.card_map_of_injective hf).symm
        _ = Nat.card ↥(S ⊓ O.map f) := Nat.card_congr (MulEquiv.subgroupCongr hmapSO).toEquiv
    rcases hdisj (S.comap f) hS₀P hS₀perf with h1 | h2 | h3
    · left; rwa [hcardS, hcardSO] at h1
    · right; left; rwa [hcardS, hcardSO] at h2
    · right; right; rwa [hcardS, hcardSO] at h3

end CFSG.RankThree.GF2n.Stroth80
end
