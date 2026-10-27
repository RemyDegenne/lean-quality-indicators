@[expose] public section

namespace FirstOrder.Language

variable (J : Type) [LinearOrder J]

/-- The **rank** of `j` in a finite support `S`: the number of support elements below it, i.e. its
0-indexed position in the increasing `J`-order. So a support `{j₀ < j₁ < …}` has ranks `0, 1, …`
and the deep interpretation sends it to `a_d, a_{d+1}, …` (a strictly-increasing deep tuple). -/
def deepRank (S : Finset J) (j : J) : ℕ := (S.filter (· < j)).card

end FirstOrder.Language
end
