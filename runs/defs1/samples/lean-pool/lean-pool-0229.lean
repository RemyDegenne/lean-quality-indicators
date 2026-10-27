@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

/-- A concrete member of the exact Davis--Kahan norm class: the nuclear norm. -/
noncomputable def nuclearNormingFunction : SymmetricNormingFunction :=
  nuclearAxiomatic.toNormingFunction

end
end ExactSinTheta
end DavisKahan
end TauCeti
end
