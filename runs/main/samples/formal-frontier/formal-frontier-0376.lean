@[expose] public section

universe u

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) [AddGroup.FG L]
  (n : ℕ)

theorem natCard_ker_nsmul_quotient
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    Nat.card (nsmulAddMonoidHom (α := V ⧸ L) n).ker = n ^ Module.finrank ℤ L := by
  have hinjL : Function.Injective (nsmulAddMonoidHom (α := L) n) := by
    intro a b hab
    exact Subtype.ext (hn.1 (congrArg Subtype.val hab))
  calc
    _ = Nat.card (L ⧸ (nsmulAddMonoidHom (α := L) n).range) :=
      Nat.card_congr (nsmulTorsionEquivQuotient L n hn).toEquiv
    _ = (nsmulAddMonoidHom (α := L) n).range.index :=
      (AddSubgroup.index_eq_card _).symm
    _ = n ^ Module.finrank ℤ L :=
      AddSubgroup.index_range_nsmul_of_injective (A := L) n hinjL

end QuotientAddGroup
end
