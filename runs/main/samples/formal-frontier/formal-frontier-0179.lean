set_option warningAsError true

@[expose] public section

noncomputable section

namespace GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

theorem finiteType_of_finiteType [Algebra.FiniteType (𝒮 0) S]
    (n : ℕ) (hn : 0 < n) :
    Algebra.FiniteType (component 𝒮 n 0) (VeroneseRing 𝒮 n) := by
  classical
  obtain ⟨F, hF, hdegree⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒮
  let w (i : F) : ℕ := (hdegree i.1 i.2).choose
  let x (i : F) : 𝒮 (w i) := ⟨i.1, (hdegree i.1 i.2).choose_spec.2⟩
  have hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i : F => (x i : S))) = ⊤ := by
    have heq : Set.range (fun i : F => (x i : S)) = (F : Set S) := by
      apply Set.ext
      intro s
      constructor
      · rintro ⟨i, rfl⟩
        exact i.2
      · intro hs
        exact ⟨⟨s, hs⟩, rfl⟩
    rw [heq]
    exact hF
  exact finiteType_of_finite_homogeneous_generators 𝒮 w x hgen n hn

end GradedRing.Veronese
end
end
