public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative

section Neg

variable {K : Type} [Field K] [Fintype K] (g : K[X]) [Fact (Irreducible g)] {n s r p : ℕ}
  [NeZero p] [Fact p.Prime] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}

theorem negMove_torusAct (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (i : Fin s) (t : Fin s → ZMod p)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    negMove g i (torusAct g (fun m => (t m).val) x) =
      torusAct g (fun m => (negMap i t m).val) (negMove g i x) := by
  refine Prod.ext (funext fun m => ?_) rfl
  rw [negMove_apply, negMove_apply]
  change negTau g i m (AdjoinRoot.root g ^ (t m).val * x.1 m) =
    AdjoinRoot.root g ^ ((negMap i t m).val) * negTau g i m (x.1 m)
  by_cases hm : m = i
  · subst m
    have hneg : AdjoinRoot.root g ^ ((negMap i t i).val) =
        (AdjoinRoot.root g ^ (t i).val)⁻¹ := by
      rw [negMap, Function.update_self]
      exact root_pow_neg_val hζ (t i)
    rw [negTau_apply_self]
    rw [map_mul, map_pow, frobAlgEquiv_root g hζ hpK, inv_pow, hneg]
  · rw [negTau_apply_of_ne g hm, negMap, Function.update_apply, if_neg hm]
    rfl

end Neg
end CFSG.StandardType.SlNsRootGen
end
