public section

open MvPolynomial Polynomial Set

namespace TauCeti

variable {n : ℕ}

section Lifting

variable [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)} {B : Finset (MvPolynomial (Fin n) ℝ)[X]}

theorem exists_isSemialgebraicStack_orderAt_eq_of_mcCallumProjection
    (hB : (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B)
    {C : Set (Fin n → ℝ)} {d : ℕ} (hC : IsSemialgebraic C) (hCa : IsAnalyticSubmanifold d C)
    (hconn : IsPreconnected C)
    (hproj : ∀ q ∈ (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B,
      ∀ x ∈ C, ∀ y ∈ C, q.orderAt x = q.orderAt y)
    (hfiber : C.Nontrivial → ∀ b ∈ B, ∀ x ∈ C, b.map (MvPolynomial.eval x) ≠ 0) :
    ∃ (k : ℕ) (θ : Fin k → C → ℝ), IsSemialgebraicStack C θ ∧
      ∀ E ∈ stackCells C θ, (∃ e, IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F, ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  rcases C.subsingleton_or_nontrivial with hs | hnt
  · -- Over a point, refine the line by the roots of the delineating polynomials.
    obtain ⟨α, hα⟩ := hCa.nonempty
    obtain rfl := hs.eq_singleton_of_mem hα
    obtain ⟨k, c, hstack, -, -, hcells⟩ := F.exists_isSemialgebraicStack_orderAt_eq α
    exact ⟨k, _, hstack, fun E hE ↦
      ⟨(hcells E hE).1.imp fun _ h ↦ h.2, fun f hf ↦ ((hcells E hE).2 f hf).1⟩⟩
  · obtain ⟨D, hD⟩ :=
      hB.exists_delineation_orderAt_eq_of_mcCallumProjection hCa hconn (hfiber hnt) hproj
    refine ⟨D.count, D.root, D.isSemialgebraicStack (φ := RingHom.id ℝ) hC, fun E hE ↦
      ⟨(hD E hE).1.imp fun _ h ↦ h.2, fun f hf ↦ ?_⟩⟩
    simpa using ((hD E hE).2 (finSuccEquiv ℝ n f) (by simpa using hf)).1

end Lifting
end TauCeti
end
