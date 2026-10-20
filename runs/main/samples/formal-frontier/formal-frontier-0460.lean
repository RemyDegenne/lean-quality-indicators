@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

theorem powerRootMap_faithfullyFlat (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    faithfullyFlatTestMorphisms K (powerRootMap K n A a).op := by
  change (AdjoinRoot.of (powerRootPolynomial K n A a)).FaithfullyFlat
  rw [← AdjoinRoot.algebraMap_eq (f := powerRootPolynomial K n A a),
    RingHom.faithfullyFlat_algebraMap_iff]
  haveI := powerRootAlgebra_free K n A a hn
  by_cases h : Subsingleton (A.obj : Type u)
  · letI : Subsingleton (A.obj : Type u) := h
    apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal
      (A.obj : Type u) (AdjoinRoot (powerRootPolynomial K n A a))).2
    exact ⟨inferInstance, fun I hI => (hI (Subsingleton.elim I ⊤)).elim⟩
  · haveI : Nontrivial (A.obj : Type u) := not_subsingleton_iff_nontrivial.mp h
    have hp : (powerRootPolynomial K n A a).Monic :=
      Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)
    have hd : 0 < (powerRootPolynomial K n A a).degree := by
      rw [powerRootPolynomial, Polynomial.degree_X_pow_sub_C hn]
      exact_mod_cast hn
    haveI : Nontrivial (AdjoinRoot (powerRootPolynomial K n A a)) :=
      (AdjoinRoot.of.injective_of_monic_of_degree_pos hp hd).nontrivial
    infer_instance

end General
end AlgebraicGeometry
end
