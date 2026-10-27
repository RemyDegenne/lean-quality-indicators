public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]

theorem centralizerArbitraryKernel_oddCore_map [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (CFSG.oddCore K).map K.subtype = centralizerOddCore n S e := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_oddCore_map n hn S e

end CFSG.Wreathed
end
