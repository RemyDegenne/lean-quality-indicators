public section

open CategoryTheory Limits

open scoped Simplicial

namespace TauCeti

namespace SSet.S1

@[ext]
lemma hom_ext {X : SSet} {f g : SSet.S1 ⟶ X} (h : quotient ≫ f = quotient ≫ g) : f = g :=
  coequalizer.hom_ext h

end SSet.S1
end TauCeti
end
