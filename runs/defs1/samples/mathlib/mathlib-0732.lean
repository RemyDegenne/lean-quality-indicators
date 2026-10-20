@[expose] public section

open scoped SetRel

variable {α : Type*} (r : SetRel α α)

variable {β : Type*} (s : SetRel β β)

namespace RelSeries

variable {r s}

/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` appended with one element.
-/
@[elab_as_elim]
def inductionOn' (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (snoc : (p : RelSeries r) → (x : α) → (hx : p.last ~[r] x) → (hp : motive p) →
      motive (p.snoc x hx)) (p : RelSeries r) :
    motive p := by
  let {n : ℕ} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert singleton p.head
      ext n
      · exact heq
      · simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have ne0 : p.length ≠ 0 := by simp [heq]
      have len : p.eraseLast.length = d := by simp [heq]
      convert snoc p.eraseLast p.last (p.eraseLast_last_rel_last ne0) (hd _ len)
      exact (p.snoc_self_eraseLast ne0).symm
  exact this rfl

end RelSeries
end
