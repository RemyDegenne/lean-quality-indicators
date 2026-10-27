public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

theorem smallReeCheck_comm
    : ∀ p ∈ smallReeCommPairs,
    wordCheck Tag.G2 3 (smallReeLeft p.1 p.2) (smallReeRight p.1 p.2 []) = true := by
  simp only [smallReeCommPairs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true]
  exact ⟨smallReeCheck_0_3, smallReeCheck_0_4, smallReeCheck_0_5, smallReeCheck_1_2,
    smallReeCheck_1_3, smallReeCheck_1_5, smallReeCheck_2_3, smallReeCheck_2_4, smallReeCheck_2_5,
    smallReeCheck_3_4, smallReeCheck_3_5, smallReeCheck_4_5⟩

end CFSG.LieType.Ree
end
