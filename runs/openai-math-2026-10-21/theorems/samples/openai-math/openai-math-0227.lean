namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem prefixBlocks_eq_mapDomain {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc)) = Finsupp.mapDomain (blockIndex c) x := by
  classical
  have hrepr := C00.ofArray_restrict x (c (Fin.last r)) hx
  change prefixBlocksLinear c x = Finsupp.mapDomain (blockIndex c) x
  calc
    prefixBlocksLinear c x = prefixBlocksLinear c
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) :=
      congrArg (prefixBlocksLinear c) hrepr.symm
    _ = ∑ i : Fin (c (Fin.last r)),
        prefixBlocksLinear c (Finsupp.single i.val (x i.val)) := by
      simp only [C00.ofArray, C00.place, map_sum]
    _ = ∑ i : Fin (c (Fin.last r)),
        Finsupp.single (blockIndex c i.val) (x i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prefixBlocksLinear_single c hc h0 i.val i.isLt (x i.val)
    _ = Finsupp.mapDomain (blockIndex c)
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) := by
      rw [C00.mapDomain_ofArray]
      rfl
    _ = Finsupp.mapDomain (blockIndex c) x :=
      congrArg (Finsupp.mapDomain (blockIndex c)) hrepr

end MarkovSuperreflexivity
end
end OAI
