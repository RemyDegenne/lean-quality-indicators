@[expose] public section

namespace ChipFiring

open Multiset Finset

/-- The configuration $c(\mathcal{O})$ associated to an acyclic orientation $\mathcal{O}$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 4.7
(part 2). -/
def orientationToConfig (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclicWithUniqueSource G O q) : Config G q :=
  configOfSource hO

end ChipFiring
end
