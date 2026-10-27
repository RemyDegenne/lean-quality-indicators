public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X : Type} [Group X] {E : Set X}

namespace Symplectic

section Cases

variable (hP : Pair X E) (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
  (hsymp : IsSymplecticType E)
  (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
    c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e)

theorem classicalConclusion_sym (hTN : (sympConfig hP hZ hS hsymp htrans).TN) :
    ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : X ≃* Equiv.Perm (Fin m), ∀ g : X, g ∈ E ↔ (φ g).IsSwap := by
  have := Pair.finite hP
  have : Finite (SympModule E) := Module.finite_of_finite (ZMod 2)
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  exact (sympConfig hP hZ hS hsymp htrans).exists_mulEquiv_perm hTN (rho hP)
    (rho_injective hP hZ hS hsymp) (sympForm_rho hP) (rho_mem_range_bar_iff hP) E bar
    (fun d => ⟨d, rfl⟩) (rho_apply_eq hP hsymp) (fun v hv => hv) ⟨bar ⟨e₀, he₀⟩, ⟨e₀, he₀⟩, rfl⟩

end Cases
end Symplectic
end CFSG.Fischer.Classification
end
