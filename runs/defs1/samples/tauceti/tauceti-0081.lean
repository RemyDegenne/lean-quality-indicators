public section

universe u v

namespace TauCeti.Excellence

/-- A commutative ring `R` is *universally catenary* if it is Noetherian and every `R`-algebra of
finite type is catenary. The condition is stated for algebras in the universe of `R`; see
`IsUniversallyCatenary.isCatenary_of_finiteType` for algebras in an arbitrary universe.
Stacks, Definition 10.105.3 (00NL). -/
class IsUniversallyCatenary (R : Type u) [CommRing R] : Prop where
  /-- A universally catenary ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- Every finite type algebra over a universally catenary ring is catenary. -/
  forall_isCatenary : ∀ (B : Type u) [CommRing B] [Algebra R B], Algebra.FiniteType R B →
    IsCatenary B

end TauCeti.Excellence
end
