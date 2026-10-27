@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- The comparison for a subset of the infinite-exponent support uses only
procyclicity and the one supplied topological generator. -/
noncomputable def residuePowerQuotientNatIsoOfInfiniteSupport
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes) (hS : S ⊆ {p | hG.exponents p = ⊤}) :
    residueDiagram.{u} S ≅ powerQuotientDiagram G hG S :=
  residuePowerQuotientNatIso G hG g hg S
    (powerImage_index_eq_of_infiniteSupport G hG S hS)

end ProfiniteGrp
end
