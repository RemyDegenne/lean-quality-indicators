public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.Blueprint

namespace InnerDiagSU

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem longRootHom_mem_last {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2)
    (z : traceZero (unitaryInvolution F 2 f)) :
    longRootHom _ (lowIdx_ne_rev k k) (Multiplicative.ofAdd z) ∈
        rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1) ∧
      longRootHom _ (rev_ne_rev_rev (lowIdx_ne_rev k k)) (Multiplicative.ofAdd z) ∈
        rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1) := by
  have hσ := unitaryInvolution_involutive hF
  have hp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hp
  by_cases he : Even n
  · exact ⟨longRootHom_mem hσ hp (toStd_last_even hk he).symm _,
      longRootHom_mem hσ hp' (toStd_neg_last_even hk he).symm _⟩
  · have hm := rev_midIdx he
    have hpm : lowIdx k ≠ midIdx n he := fun h => hp (by rw [← h] at hm; exact hm.symm)
    have hpm' : Fin.rev (lowIdx k) ≠ midIdx n he := fun h => hp' (by
      rw [← h] at hm; exact hm.symm)
    have hz : (z : F) + unitaryInvolution F 2 f z + unitaryInvolution F 2 f 0 * 0 = 0 := by
      rw [mul_zero, add_zero]
      exact (mem_traceZero _).mp z.2
    refine ⟨heisenberg_le hσ hp hpm hm (toStd_last_odd hk he).symm ⟨0, z, hz, ?_⟩,
      heisenberg_le hσ hp' hpm' hm (toStd_neg_last_odd hk he).symm ⟨0, z, hz, ?_⟩⟩
    · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, heisenbergMatrix]
      simp
    · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, heisenbergMatrix]
      simp

end Main
end InnerDiagSU
end CFSG.StandardType
end
