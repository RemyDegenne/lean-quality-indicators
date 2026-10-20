namespace P2MW.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt

set_option autoImplicit false

universe u v

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    [Algebra.QuasiFiniteAt R q] :
    Module.Finite R (Localization.AtPrime q) :=
  HenselFiniteAt.moduleFinite_localization q hq

end P2MW.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
