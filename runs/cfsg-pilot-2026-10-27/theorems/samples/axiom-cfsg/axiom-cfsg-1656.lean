public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

theorem ggSecFiveRankOneInPerfInput_holds :
    GGSecFiveRankOneInPerfInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrA hrC
  obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
    ggSecFiveKGPosInput_holds G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hW : GGIsWeylMatrix (coxeterMatrix (ggU t n f).D.isFiniteType) :=
    (ggTag_weylMatrix htag hadm).1
  have h3ψ : ∀ i j : Fin (ggU t n f).D.rank, i ≠ j →
      (coxeterMatrix (ggU t n f).D.isFiniteType).M i j ≤ 3 :=
    (ggTag_weylMatrix htag hadm).2
  have hpresψ : GGCoxeterPres p (ggAutomizer X Bs)
      (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨hW, hεrefl⟩
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hrCox : r ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpresψ h3ψ hrA hrefl
  obtain ⟨w, i, hw⟩ := hrCox
  have hlevi : ggRankOneIn X Bs r =
      (ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ := by
    rw [hw]
    exact hεlevi w i
  have hperf_levi : ⁅ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)),
      ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))⁆ =
      ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) := by
    obtain ⟨ν, hν⟩ := (ggTagFacts_of_admissible hadm h3).2.1
    have hconj := l1f_ggRootLevi_map_conj_weylLift (ggU t n f).D ν hν
      (MonoidHom.id (ggU t n f).K) w i
    have hγ_eq : ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) =
        (ggRootLevi (ggU t n f).D (Pi.single i 1)).map
          (MulAut.conj (ν w)).toMonoidHom := by
      simpa using hconj
    rw [hγ_eq]
    have hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f) :=
      ggRankOneModel_of_tag htag hadm h3
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      have hf : 1 ≤ f := hadm.2.1
      have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
        GaloisField.card 2 f (by omega)
      have hp : p.Prime := (ggRouteCfg_prime hcfg).1
      have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have h2f : 4 ≤ 2 ^ f := by
        have h2fpos : 0 < 2 ^ f - 1 := by
          have h2 : 2 ≤ 2 ^ f := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
          omega
        have hle : p ≤ 2 ^ f - 1 := Nat.le_of_dvd h2fpos hpf
        omega
      omega
    have hsimp : ⁅ggRootLevi (ggU t n f).D (Pi.single i 1),
        ggRootLevi (ggU t n f).D (Pi.single i 1)⁆ =
        ggRootLevi (ggU t n f).D (Pi.single i 1) :=
      l1f_rootLevi_perfect hM i h4
    rw [← Subgroup.map_commutator, hsimp]
  rw [hlevi, ← Subgroup.map_commutator, hperf_levi]

end CFSG.StandardType
end
