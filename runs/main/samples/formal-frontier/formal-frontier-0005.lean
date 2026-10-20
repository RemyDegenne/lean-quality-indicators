@[expose] public section

set_option warningAsError true

noncomputable section

namespace GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

theorem adjoin_component_one_eq_top (n : ℕ) (hn : 0 < n)
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    Algebra.adjoin (component 𝒮 n 0)
      (component 𝒮 n 1 : Set (VeroneseRing 𝒮 n)) = ⊤ := by
  let U : Subalgebra (component 𝒮 n 0) (VeroneseRing 𝒮 n) :=
    Algebra.adjoin (component 𝒮 n 0) (component 𝒮 n 1 : Set (VeroneseRing 𝒮 n))
  apply top_unique
  intro x _
  have h : ∀ x : VeroneseRing 𝒮 n, x ∈ U := by
   intro x
   induction x using DirectSum.induction_on with
  | zero => exact U.zero_mem
  | of j s =>
    obtain ⟨p, hhom, hp⟩ := MvPolynomial.exists_isHomogeneous_aeval 𝒮 hgen s.property
    have hmem : p ∈ (MvPolynomial.homogeneousSubmodule (𝒮 1) (𝒮 0) n) ^ j := by
      rw [← homogeneousSubmodule_mul_eq_pow 𝒮 n j]
      exact (MvPolynomial.mem_homogeneousSubmodule (n * j) p).mpr hhom
    obtain ⟨t, ht, heq⟩ := eval_mem_adjoin 𝒮 n hn j hmem
    have ht' : t = DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j s :=
      inclusion_injective 𝒮 n hn (heq.trans (hp.trans (inclusion_of 𝒮 n j s).symm))
    exact ht' ▸ ht
   | add x y hx hy => exact U.add_mem hx hy
  exact h x

end GradedRing.Veronese
end
end
