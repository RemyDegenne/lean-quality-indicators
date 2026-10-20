public section

noncomputable section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti

open TauCeti.NumberField.QuadraticForm (GlobalFormInvariants)

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The system of local invariants of a regular quadratic form** `Q` over a number field: its
rank, its plain discriminant `d(Q) ∈ Kˣ/(Kˣ)²`, its Hasse sign at every finite place and its
positive index at every real place. -/
def globalInvariants (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GlobalFormInvariants K :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  { rank := Module.finrank K V
    discr := RegularFormClass.discr (formClass Q hQ)
    finiteHasse := Q.finiteHasse hQ
    realPositiveIndex := Q.realPositiveIndex }

end QuadraticForm
end
end
