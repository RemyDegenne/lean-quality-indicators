@[expose] public section

noncomputable section

namespace LeanPool.EilenbergZilber

namespace Shuffle

/-- The **staircase** `(r,m)`-shuffle `k ↦ (min(k,r), k - r)`: it goes right `r` steps then up
`m` steps (the lexicographically smallest shuffle path). Its front-`r` face and back-`m` face
recover the identity, so it is the unique shuffle contributing the identity summand to the
diagonal Eilenberg–Zilber/Alexander–Whitney pairing. -/
def trivialShuffle (r m : ℕ) : Shuffle r m :=
  ⟨OrderHom.prod
      ⟨fun k => ⟨min k.val r, by omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩
      ⟨fun k => ⟨k.val - r, by have := k.isLt; omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩,
    fun a b hab => by
      have h1 : min a.val r = min b.val r := congrArg (fun p => (p.1 : ℕ)) hab
      have h2 : a.val - r = b.val - r := congrArg (fun p => (p.2 : ℕ)) hab
      apply Fin.ext
      have ha := a.isLt; have hb := b.isLt
      omega⟩

end Shuffle
end LeanPool.EilenbergZilber
end
end
