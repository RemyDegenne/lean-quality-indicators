public section

open scoped MonoidAlgebra ModuleCat

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G]
  (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exists_coprimePart_indK0_of_trivial_eq_nsmul [Finite G] (C : Subgroup G) [IsCyclic C] :
    ∃ D : Subgroup G, D ≤ C ∧ ¬ p ∣ Nat.card D ∧
      D.relIndex C = p ^ (Nat.card C).factorization p ∧
      (letI : Module.Finite k[D] (Representation.trivial k D k).asModule :=
        Module.Finite.of_restrictScalars_finite k k[D] _
      letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
        Module.Finite.of_restrictScalars_finite k k[C] _
      indK0 k D (ExactK0.of (FGModuleCat.of k[D] (Representation.trivial k D k).asModule)) =
        (p ^ (Nat.card C).factorization p) • indK0 k C
          (ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule))) := by
  obtain ⟨D, hDC, hDn, hDp, hpow, hindex⟩ :=
    exists_coprimePart_of_isCyclic (Fact.out : p.Prime) (C := C)
  let := hDn
  refine ⟨D, hDC, hDp, hindex, ?_⟩
  rw [← hindex]
  exact indK0_of_trivial_eq_relIndex_nsmul (k := k) p hDC hpow

end TauCeti
end
