public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral

universe u

variable {H : Type u} [Group H] {n : ℕ}

section Automizers

variable [Finite H]

theorem isConj_of_automizerIndex_qdFour_ne_two (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h2 : automizerIndex (qdFour (S : Subgroup H) f) ≠ 2) :
    IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set T := qdFour (S : Subgroup H) f with hT
  have hK : IsKleinFour T := qdFour_isKleinFour hn _ f
  have hsT : ι (s n) ∈ T := ⟨s n, s_mem_sdFourSubgroup n, rfl⟩
  have hzT : ι (z n) ∈ T := ⟨z n, z_mem_sdFourSubgroup n, rfl⟩
  obtain ⟨hS2, halt⟩ := qdFour_automizer_alternatives hn S f
  rcases halt with hGS | htop
  · exact absurd (by rw [automizerIndex_eq_card_range, hGS, hS2]) h2
  · classical
    obtain ⟨e, he⟩ := (Local.kleinFour_automorphism_action (V := T)).1
    have hs1 : (⟨ι (s n), hsT⟩ : T) ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change ι (s n) = 1 at h'
      rw [← map_one ι] at h'
      have h'' := FocalFusion.ambientHom_injective n _ f h'
      have ho := orderOf_s n (by omega)
      rw [h'', orderOf_one] at ho
      omega
    have hz1 : (⟨ι (z n), hzT⟩ : T) ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change ι (z n) = 1 at h'
      rw [← map_one ι] at h'
      exact z_ne_one n (by omega) (FocalFusion.ambientHom_injective n _ f h')
    let sT : {x : T // x ≠ 1} := ⟨⟨ι (s n), hsT⟩, hs1⟩
    let zT : {x : T // x ≠ 1} := ⟨⟨ι (z n), hzT⟩, hz1⟩
    let ψ : MulAut T := e.symm (Equiv.swap sT zT)
    have hψ : ψ ⟨ι (s n), hsT⟩ = ⟨ι (z n), hzT⟩ := by
      have h1 := he ψ sT
      rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left] at h1
      exact h1.symm
    have hψmem : ψ ∈ T.normalizerMonoidHom.range := by
      rw [htop]
      exact Subgroup.mem_top ψ
    obtain ⟨h, hh⟩ := hψmem
    refine isConj_iff.mpr ⟨h, ?_⟩
    have h1 := congrArg (fun φ : MulAut T => ((φ ⟨ι (s n), hsT⟩ : T) : H)) hh
    change (h : H) * ι (s n) * (h : H)⁻¹ = ((ψ ⟨ι (s n), hsT⟩ : T) : H) at h1
    rw [h1, hψ]

end Automizers
end CFSG.QuasiDihedralFusion
end
