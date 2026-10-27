public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

section Enum

variable {E : Enum} {gs : Array (Array ℕ)} {s : ℕ → StatedSp 3 (ZMod 2)}
  {L : Subgroup (StatedSp 3 (ZMod 2))}

theorem nat_card_subtype_eq_countLt (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) (p : Array ℕ → Bool) :
    Nat.card {x : ↥L // p (code x) = true} = countLt E.elems.size fun i => p E.elems[i]! := by
  obtain ⟨f, hf⟩ := exists_equiv_fin_of_enumOK hL hgs h
  rw [countLt_eq_nat_card]
  refine Nat.card_congr (Equiv.subtypeEquiv f fun i => ?_).symm
  rw [hf i]

end Enum
end CFSG.ClassicalInvolution.Solomon73.Yamaki
end
