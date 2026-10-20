@[expose] public section

open scoped ComplexOrder

open RCLike

open scoped ComplexConjugate

variable {𝕜 X : Type _} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open scoped ComplexConjugate

open scoped Topology BigOperators NNReal

open scoped ComplexOrder

open scoped ComplexOrder

open RCLike

open scoped InnerProductSpace

lemma example_pos_commute_iff_pos_mul_of {𝕜 R : Type _} [RCLike 𝕜] [Ring R]
  [PartialOrder R] [StarRing R] [Algebra 𝕜 R]
  (h₁ : ∀ x : R, 0 ≤ x ↔ ∃ r : R, x = star r * r)
  (h₂ : ∀ x : R, 0 ≤ x ↔ IsSelfAdjoint x ∧ spectrum 𝕜 x ⊆ { a : 𝕜 | 0 ≤ a })
  {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  Commute x y ↔ 0 ≤ x * y := by
  have : {(0 : 𝕜)} ⊆ {a : 𝕜 | 0 ≤ a} :=
  by simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq, le_refl]
  have := fun s => Set.subset_diff_inj s this
  rw [h₂, IsSelfAdjoint, star_mul, ((h₂ _).mp hx).1, ((h₂ _).mp hy).1]
  constructor
  · intro h
    refine ⟨by rw [h], ?_⟩
    obtain ⟨a, rfl⟩ := (h₁ x).mp hx
    obtain ⟨b, rfl⟩ := (h₁ y).mp hy
    rw [this]
    calc spectrum 𝕜 (star a * a * (star b * b)) \ {0}
        = spectrum 𝕜 (a * (star b * b) * star a) \ {0} :=
          by nth_rw 2 [spectrum.nonzero_mul_comm]; simp_rw [mul_assoc]
      _ = spectrum 𝕜 (star (b * star a) * (b * star a)) \ {0} := by
        simp only [star_mul, star_star, mul_assoc]
      _ ⊆ {c : 𝕜 | 0 ≤ c} \ {0} := ?_
    rw [← this]
    have this : ∀ x : R, 0 ≤ star x * x := fun x => (h₁ _).mpr ⟨x, rfl⟩
    have := fun x => ((h₂ _).mp (this x)).2
    exact this _
  · intro h
    exact h.1.symm

end
