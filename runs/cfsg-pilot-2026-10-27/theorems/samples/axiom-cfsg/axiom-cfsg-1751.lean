public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

variable {r : ℕ}

theorem hasB_iff_of_even {i j : ℤ} (hij : Even (i - j)) (d : ℕ) :
    X.HasB i d ↔ X.HasB j d := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, i - j = 2 * m := by
    obtain ⟨k, hk⟩ := hij
    exact ⟨k, by omega⟩
  have hZ : X.Z i = conjSub (X.τ ^ m) (X.Z j) := by
    rw [show i = j + 2 * m by omega, X.Z_add]
  have hGi : ∀ k : ℤ, X.Gi (i + k) = conjSub (X.τ ^ m) (X.Gi (j + k)) := by
    intro k
    rw [show i + k = (j + k) + 2 * m by omega, X.Gi_add]
  have hiff : ∀ {A B : Subgroup G},
      A ≤ B ↔ conjSub (X.τ ^ m) A ≤ conjSub (X.τ ^ m) B :=
    fun {_ _} => (Subgroup.map_le_map_iff_of_injective (MulAut.conj _).injective).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k] at h
      exact hiff.mpr h
    · intro h
      apply h2
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, X.Gi_add]
      exact hiff.mp h
    · intro h
      apply h3
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, X.Gi_add]
      exact hiff.mp h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k]
      exact hiff.mp h
    · intro h
      apply h2
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, X.Gi_add] at h
      exact hiff.mpr h
    · intro h
      apply h3
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, X.Gi_add] at h
      exact hiff.mpr h

end Setup
end CFSG.Quasithin.St84
end
