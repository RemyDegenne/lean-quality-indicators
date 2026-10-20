@[expose] public section

namespace GenLimit.FiniteWitness.Anchored

/-- Left-side anchor points assigned to a row. -/
noncomputable def rowWitness {k} (i : Fin k) : Finset Point :=
  (if i.val < (k + 1) / 2 then low k else high k).image Sum.inl

end GenLimit.FiniteWitness.Anchored
end
