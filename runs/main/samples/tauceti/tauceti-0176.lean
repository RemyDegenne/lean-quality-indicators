public section

namespace TauCeti

open PathAlgebra

universe u v w

theorem IsBasic.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker {k : Type w} {A : Type u}
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] (hA : IsBasic A) :
    ∃ (Q : Type) (_ : Quiver.{0} Q) (_ : Finite Q) (_ : ∀ i j : Q, Finite (i ⟶ j))
      (F : pathAlgebra k Q →ₐ[k] A),
      Function.Surjective F ∧ IsAdmissibleIdeal (RingHom.ker F.toRingHom) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hJ : IsNilpotent (Ring.jacobson A) := IsSemiprimaryRing.isNilpotent
  obtain ⟨n, e, he, hne, hquot⟩ := hA.exists_completeOrthogonalIdempotents (k := k)
  -- The arrows `i ⟶ j` index a basis of the `(j, i)`-corner of `J ⧸ J ^ 2`.
  let W (i j : Fin n) : Submodule k (A ⧸ Ring.jacobson A ^ 2) :=
    ((Ring.jacobson A).restrictScalars k).map
      ((Ideal.Quotient.mkₐ k (Ring.jacobson A ^ 2)).toLinearMap ∘ₗ
        LinearMap.mulLeftRight k (e j, e i))
  let : Quiver.{0} (Fin n) := ⟨fun i j => Fin (Module.finrank k (W i j))⟩
  have hlift (i j : Fin n) (t : i ⟶ j) : ∃ x ∈ Ring.jacobson A,
      Ideal.Quotient.mk (Ring.jacobson A ^ 2) (e j * x * e i) = Module.finBasis k (W i j) t := by
    obtain ⟨x, hx, hxt⟩ := Submodule.mem_map.mp (Module.finBasis k (W i j) t).2
    exact ⟨x, hx, by simpa using hxt⟩
  choose x hxJ hx using hlift
  let f : ∀ {i j : Fin n}, (i ⟶ j) → A := fun {i j} t => e j * x i j t * e i
  have hl {i j : Fin n} (t : i ⟶ j) : e j * f t = f t := by
    simp only [f, ← mul_assoc, (he.idem j).eq]
  have hr {i j : Fin n} (t : i ⟶ j) : f t * e i = f t := by
    simp only [f, mul_assoc, (he.idem i).eq]
  have hbasis (i j : Fin n) : (fun t : i ⟶ j => Ideal.Quotient.mk (Ring.jacobson A ^ 2) (f t)) =
      (W i j).subtype ∘ Module.finBasis k (W i j) := funext (hx i j)
  refine ⟨Fin n, inferInstance, inferInstance,
    fun i j => inferInstanceAs (Finite (Fin (Module.finrank k (W i j)))),
    liftAlgHomOfArrows k e he f hl hr, ?_, ?_⟩
  · refine liftAlgHomOfArrows_surjective e he f hl hr _ hJ hquot fun i j y hy => ?_
    rw [hbasis, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
      Submodule.range_subtype]
    exact Submodule.mem_map_of_mem
      (f := (Ideal.Quotient.mkₐ k (Ring.jacobson A ^ 2)).toLinearMap ∘ₗ
        LinearMap.mulLeftRight k (e j, e i)) hy
  · refine isAdmissibleIdeal_ker_liftAlgHomOfArrows e he f hl hr _ hJ hne
      (fun {i j} t => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hxJ i j t))) fun i j => ?_
    rw [hbasis]
    exact (Module.finBasis k (W i j)).linearIndependent.map' _ (Submodule.ker_subtype _)

end TauCeti
end
