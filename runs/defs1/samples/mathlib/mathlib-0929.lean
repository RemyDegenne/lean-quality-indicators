@[expose] public section

namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

/-- The `PNat` version of `Nat.findX` -/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ) (n : ℕ+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using! pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩

end PNat
end
