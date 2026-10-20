@[expose] public section

universe uR uι uκ uM uN

namespace LinearMap

theorem traceOfFiniteProjective_pi
    (R : Type uR) [CommSemiring R]
    {ι : Type uι} [Finite ι]
    (M : ι → Type uM)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)]
    (f : (∀ i, M i) →ₗ[R] (∀ i, M i)) :
    traceOfFiniteProjective R (∀ i, M i) f =
      ∑ᶠ i : ι, traceOfFiniteProjective R (M i)
        ((LinearMap.proj (R := R) (φ := M) i).comp
          (f.comp (@LinearMap.single R ι _ M _ _ (Classical.decEq ι) i))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hsum : (∑ i : ι, (f.comp (single R M i)).comp (proj i)) = f := by
    simpa only [lsum_apply, lsum_symm_apply] using
      (lsum R M R).apply_symm_apply f
  rw [finsum_eq_sum_of_fintype]
  calc
    traceOfFiniteProjective R (∀ i, M i) f =
        traceOfFiniteProjective R (∀ i, M i)
          (∑ i : ι, (f.comp (single R M i)).comp (proj i)) :=
      congrArg (traceOfFiniteProjective R (∀ i, M i)) hsum.symm
    _ = ∑ i : ι, traceOfFiniteProjective R (∀ i, M i)
        ((f.comp (single R M i)).comp (proj i)) := by rw [map_sum]
    _ = ∑ i : ι, traceOfFiniteProjective R (M i)
        ((proj i).comp (f.comp (single R M i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact traceOfFiniteProjective_comp_comm R (∀ i, M i) (M i)
        (proj i) (f.comp (single R M i))

end LinearMap
end
