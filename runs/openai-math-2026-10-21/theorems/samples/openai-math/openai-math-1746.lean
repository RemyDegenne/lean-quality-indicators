namespace OAI

namespace TuringRigidity.CodingSplitting

open CodingForcing

theorem split_or_divergent_word {Y : Oracle} {e : OracleCode} {base s t : List Bool}
    (hs : base <+: s) (ht : base <+: t) (n a b : ℕ)
    (ha : a ∈ CommonIdeal.run Y e s n) (hb : b ∈ CommonIdeal.run Y e t n) (hab : a ≠ b) :
    OnePoint base (fun w => CommonIdeal.run Y e w n) ∨
      ∃ w, base <+: w ∧ ∀ u v, v ∉ CommonIdeal.run Y e (w ++ u) n := by
  by_cases hd : ∀ w, base <+: w → ∃ u v, v ∈ CommonIdeal.run Y e (w ++ u) n
  · exact Or.inl (onePoint_of_dense (fun h v hv => CommonIdeal.run_mono h n v hv)
      hd hs ht a b ha hb hab)
  · right
    push Not at hd
    exact hd

end TuringRigidity.CodingSplitting
end OAI
