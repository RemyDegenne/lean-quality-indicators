@[expose] public section

set_option warningAsError true

open CategoryTheory

open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

theorem not_birational_spec_field_spec_polynomial (K k : Type u) [Field K] [Field k] :
    ¬Birational (Spec (CommRingCat.of K)) (Spec (CommRingCat.of k[X])) := by
  have hNontrivial : Nontrivial (Spec (CommRingCat.of k[X])) := nontrivial_spec_polynomial k
  exact @not_birational_of_subsingleton_of_jacobson _ _ _ _ hNontrivial

end AlgebraicGeometry.Scheme
end
