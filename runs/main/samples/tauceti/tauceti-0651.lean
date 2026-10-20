public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

section Structure

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

theorem spinAction_bijective (h : Even (finrank K V)) :
    Function.Bijective (spinAction Q P) :=
  ⟨spinAction_injective P h, spinAction_surjective P⟩

end Structure
end TauCeti
end
