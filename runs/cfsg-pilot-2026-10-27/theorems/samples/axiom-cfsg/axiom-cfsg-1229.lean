public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem word_act :
    ∀ w : List ℤ, (∀ l ∈ w, 0 < l ∧ l ≤ 4) → ∀ x : Fin 50,
    ∃ h : evalPos a6Sm w x < 50, wordVal a6Gen w • omPt x = omPt ⟨evalPos a6Sm w x, h⟩
  | [], _, x => ⟨x.2, by rw [wordVal_nil, one_smul]; rfl⟩
  | l :: w, hw, x => by
    obtain ⟨h1, he⟩ := word_act w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) x
    have hl := hw l (List.mem_cons_self ..)
    have hk : l.toNat - 1 < 4 := by omega
    have e1 : (if 0 < l then a6Gen (l.natAbs - 1) else (a6Gen (l.natAbs - 1))⁻¹) =
        a6Gen (l.toNat - 1) := by
      rw [ite_eq_left hl.1, show l.natAbs - 1 = l.toNat - 1 by omega]
    obtain ⟨h2, he2⟩ := a6_act hk ⟨evalPos a6Sm w x, h1⟩
    rw [wordVal_cons, e1, mul_smul, he, he2]
    exact ⟨h2, rfl⟩

end CFSG.Sporadic.HNOddCore
end
