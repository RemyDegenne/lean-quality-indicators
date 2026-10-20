@[expose] public section

open scoped PowerSeries.WithPiTopology

theorem pentagonal_injective'' : Function.Injective pentagonal'' := by
  intro a b h
  have : a * (3 * a - 1) = b * (3 * b - 1) := by
    simp [← two_pentagonal'', h]
  apply two_pentagonal_inj'' this

end
