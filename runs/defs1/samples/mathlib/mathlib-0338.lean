@[expose] public section

universe u

namespace Ordnode

variable {α : Type*}

local prefix:arg "ι" => Ordnode.singleton

/-- Auxiliary definition for `ofAscList`.

**Note:** This function is defined by well-founded recursion, so it will probably not compute
in the kernel, meaning that you probably can't prove things like
`ofAscList [1, 2, 3] = {1, 2, 3}` by `rfl`.
This implementation is optimized for VM evaluation. -/
def ofAscListAux₁ : ∀ l : List α, ℕ → Ordnode α × { l' : List α // l'.length ≤ l.length }
  | [] => fun _ => (nil, ⟨[], le_rfl⟩)
  | x :: xs => fun s =>
    if s = 1 then (ι x, ⟨xs, Nat.le_succ _⟩)
    else
      match ofAscListAux₁ xs (s <<< 1) with
      | (t, ⟨[], _⟩) => (t, ⟨[], Nat.zero_le _⟩)
      | (l, ⟨y :: ys, h⟩) =>
        have := Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by l => l.length

end Ordnode
end
