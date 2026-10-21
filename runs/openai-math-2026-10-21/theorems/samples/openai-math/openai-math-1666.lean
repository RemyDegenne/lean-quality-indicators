namespace OAI

noncomputable section

open scoped TensorProduct

namespace Lech.ReesRoot

open UniversalSplitting ProductSourceCover

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)

attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance

private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance

private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

lemma sectionsRestriction_smul {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (m : Fin n → ℤ) (hst : s ⊆ t) (a : Ring I z hz s) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht m hst (a • x)=
      restriction I z hz hst a • sectionsRestriction I z hz hs ht m hst x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      simp only [TensorProduct.smul_tmul',smul_eq_mul,sectionsRestriction_tmul,map_mul]
  | add x y hx hy => rw [smul_add,map_add,map_add,hx,hy,smul_add]

end Lech.ReesRoot
end
end OAI
