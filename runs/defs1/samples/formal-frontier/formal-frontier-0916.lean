set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

/-- Multiplicative facade for the quotient by the closure of `n`-th powers. -/
abbrev TopologicalPowerQuotient (A : Type uA) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) :=
  A ⧸ TopologicalPowerQuotient.closedPowers A n

end
end
