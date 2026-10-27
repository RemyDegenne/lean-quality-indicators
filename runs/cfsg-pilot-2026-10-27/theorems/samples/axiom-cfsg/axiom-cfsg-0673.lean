public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

theorem exists_index_two_of_sylow_card {X : Type} [Group X] [Finite X] {J : Subgroup X} [J.Normal]
    (T : Sylow 2 X) (h : Nat.card ↥(T : Subgroup X) = 2 * Nat.card ↥((T : Subgroup X) ⊓ J)) :
    ∃ N : Subgroup X, N.Normal ∧ J ≤ N ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := J)
  have hP1 : Nat.card ↥P = Nat.card ↥((T : Subgroup X) ⊓ J) := by
    have : Nat.card ↥((T : Subgroup X) ⊓ J) = Nat.card ↥(((T : Subgroup X) ⊓ J).subgroupOf J) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    rw [this, ← hP]
    rfl
  have hTcard : Nat.card ↥(T : Subgroup X) = 2 ^ (Nat.card X).factorization 2 :=
    Sylow.card_eq_multiplicity T
  have hPcard : Nat.card ↥P = 2 ^ (Nat.card ↥J).factorization 2 := Sylow.card_eq_multiplicity P
  have hXQ : Nat.card X = Nat.card (X ⧸ J) * Nat.card ↥J := Subgroup.card_eq_card_quotient_mul_card_subgroup J
  have hQpos : Nat.card (X ⧸ J) ≠ 0 := Nat.card_pos.ne'
  have hJpos : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card X).factorization 2 = (Nat.card (X ⧸ J)).factorization 2 + (Nat.card ↥J).factorization 2 := by
    rw [hXQ, Nat.factorization_mul hQpos hJpos]
    rfl
  have h2 : 2 ^ (Nat.card X).factorization 2 = 2 * 2 ^ (Nat.card ↥J).factorization 2 := by
    rw [← hTcard, h, hP1.symm.trans hPcard]
  have hq1 : (Nat.card (X ⧸ J)).factorization 2 = 1 := by
    have : 2 ^ ((Nat.card (X ⧸ J)).factorization 2 + (Nat.card ↥J).factorization 2) =
        2 ^ (1 + (Nat.card ↥J).factorization 2) := by
      rw [← hfac, h2, pow_add, pow_one]
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  obtain ⟨R⟩ : Nonempty (Sylow 2 (X ⧸ J)) := inferInstance
  have hR : Nat.card ↥(R : Subgroup (X ⧸ J)) = 2 := by
    have := Sylow.card_eq_multiplicity R
    rw [hq1] at this
    simpa using this
  have hcyc : IsCyclic ↥(R : Subgroup (X ⧸ J)) := isCyclic_of_prime_card (p := 2) hR
  have : Fintype (X ⧸ J) := Fintype.ofFinite _
  have hQeven : Even (Fintype.card (X ⧸ J)) := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.2 (Nat.dvd_of_factorization_pos (by omega))
  obtain ⟨-, hsurj, hnorm, hidx⟩ := LinearGroups.cyclic_sylow_index_two hQeven R hcyc
  let ε := Equiv.Perm.sign.comp (MulAction.toPermHom (X ⧸ J) (X ⧸ J))
  refine ⟨ε.ker.comap (QuotientGroup.mk' J), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.comap hnorm _
  · intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    have : (QuotientGroup.mk' J) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [this, map_one]
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective J)]
    exact hidx

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
end
