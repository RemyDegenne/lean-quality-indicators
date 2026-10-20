public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

@[simp]
theorem cup_cupH0_assoc (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P q) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cup (M ⊗ N) P p q r h (cupH0 M N p x y) z) =
      cup M (N ⊗ P) p q r h x (cup0H N P q y z) := by
  simpa only [cup_zero_right, cup_zero_left] using cup_assoc M N P (add_zero p) (zero_add q) h x y z

end TauCeti.TateCohomology
end
