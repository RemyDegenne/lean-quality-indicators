public section

open NumberField WeierstrassCurve QuadraticAlgebra IsDedekindDomain

namespace TauCeti.WorkedExamples

/-- The elliptic curve `y² = x³ + (-15221331 θ - 53748576) x + (-79617688290 θ - 281140318368)`
over `ℚ(√65)`, with `θ = (1 + √65) / 2`. -/
noncomputable def curveSqrt65 : WeierstrassCurve QSqrt65 :=
  ⟨0, 0, 0, -15221331 * (sqrt65Theta : QSqrt65) - 53748576,
    -79617688290 * (sqrt65Theta : QSqrt65) - 281140318368⟩

end TauCeti.WorkedExamples
end
