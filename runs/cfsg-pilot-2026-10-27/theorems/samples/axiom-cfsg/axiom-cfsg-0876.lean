public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

section Edge

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {K : Type} [Field K]

theorem exists_two_pow_five_sign (h2 : (-1 : K) ≠ 1) (a b : Fin 5 → ι) (hab : ∀ k, a k ≠ b k)
    (hind : ∀ v : V2 5, (∀ x y, edgeVec a b v x = edgeVec a b v y) → v = 1)
    (H : Subgroup (GL ι K)) (hH : ∀ v : ι → C2, ∏ x, v x = 1 → signD K v ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_statedProj H (fun v => signD K (edgeVec a b v)) ?_ ?_ ?_
  · intro v
    exact hH _ (prod_edgeVec a b hab v)
  · intro v w
    have : signD K (edgeVec a b (v * w)) = signD K (edgeVec a b v) * signD K (edgeVec a b w) := by
      rw [map_mul, ← signDHom_apply, ← signDHom_apply, ← signDHom_apply, map_mul]
    rw [this, inv_mul_cancel]
    exact one_mem _
  · intro v hv
    exact hind v fun x y => eps_inj h2 (signD_scalar hv x y)

end Edge
end CFSG.RankThree.PartOne.SLB4A
end
