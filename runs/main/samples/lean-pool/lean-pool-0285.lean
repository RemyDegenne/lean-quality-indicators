@[expose] public section

noncomputable section

namespace NRR

open scoped BigOperators

variable {p d : Nat}

namespace FoxNeuwirthOrderComplex

namespace SimplicialChain

section

variable {R : Type*} [CommRing R]

omit [CommRing R] in
theorem relabel_mul
    (sigma tau : Equiv.Perm (Fin p))
    (chain : SimplicialChain R p d) :
    relabel (sigma * tau) chain = relabel sigma (relabel tau chain) := by
  funext s
  simp only [relabel_apply]
  congr 1

end
end SimplicialChain
end FoxNeuwirthOrderComplex
end NRR
end
end
