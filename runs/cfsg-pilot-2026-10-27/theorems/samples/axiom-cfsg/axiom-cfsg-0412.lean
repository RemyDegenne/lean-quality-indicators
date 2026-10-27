public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sz32Local

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.RankThree.PartOne.K159.SzAbs (SzSylow)

namespace Sz32Normal

variable {X : Type} [Group X] {K : Subgroup X}

variable [Finite X]

theorem card_sylow_inf (hK : Sz32Normal K) (R : Sylow 5 X) :
    Nat.card ((R : Subgroup X) ⊓ K : Subgroup X) = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKn := hK.normal
  apply le_antisymm
  · have hp : IsPGroup 5 (((R : Subgroup X) ⊓ K).subgroupOf K) :=
      (R.isPGroup'.to_inf_left).comap_subtype
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    calc Nat.card ((R : Subgroup X) ⊓ K : Subgroup X)
        = Nat.card (((R : Subgroup X) ⊓ K).subgroupOf K) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
      _ ≤ Nat.card (S : Subgroup K) := Subgroup.card_le_of_le hS
      _ = 25 := (hK.data S).card_eq
  · obtain ⟨S₀⟩ : Nonempty (Sylow 5 K) := inferInstance
    set S : Subgroup X := (S₀ : Subgroup K).map K.subtype with hSdef
    have hSc : Nat.card S = 25 := by
      rw [hSdef, Subgroup.card_map_of_injective K.subtype_injective]
      exact (hK.data S₀).card_eq
    have hSp : IsPGroup 5 S := IsPGroup.of_card (n := 2) (by rw [hSc]; norm_num)
    obtain ⟨Q, hSQ⟩ := hSp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
    have hQR : (R : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    have hle : S.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup X) ⊓ K := by
      refine le_inf (hQR ▸ Subgroup.map_mono hSQ) ?_
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, -, rfl⟩ := hs
      exact hKn.conj_mem _ k.2 g
    calc 25 = Nat.card (S.map (MulAut.conj g).toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hSc]
      _ ≤ _ := Subgroup.card_le_of_le hle

end Sz32Normal
end CFSG.AGLEmbeddingD2
end
