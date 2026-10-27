@[expose] public section

open Filter Asymptotics Real Set MeasureTheory

open Complex

open scoped ComplexConjugate

open scoped Topology

namespace Complex

/-- Deligne's archimedean Gamma factor for a real infinite place.

See "Valeurs de fonctions L et périodes d'intégrales" § 5.3. Note that this is not the same as
`Real.Gamma`; in particular it is a function `ℂ → ℂ`. -/
noncomputable def Gammaℝ (s : ℂ) := π ^ (-s / 2) * Gamma (s / 2)

end Complex
end
