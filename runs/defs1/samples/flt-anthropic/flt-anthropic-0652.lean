set_option autoImplicit false

open scoped Quaternion

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

namespace Rigidification

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

def Equiv (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) : Prop :=
  ∃ (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A), IsComparison ρ₁ ρ₂ u uA ∧
    ∃ i j : ℕ, u ≫ ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

end Rigidification
end CerednikDrinfeld.QM.FakeEllipticCurve
