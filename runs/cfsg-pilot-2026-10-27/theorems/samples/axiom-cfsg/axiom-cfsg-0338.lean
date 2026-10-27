public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

section Orthogonal

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) (hρ : IsIsomRep β ρ)

variable [Finite A]

variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hρ hp hA hpK in
theorem weightFamily_orthogonal {i j : Option (Hyperplane A p)} (hij : i ≠ j) {v w : V}
    (hv : v ∈ weightFamily (p := p) ρ i) (hw : w ∈ weightFamily (p := p) ρ j) : β v w = 0 := by
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  rw [eps_left β ρ hρ i, ← Module.End.mul_apply,
    (orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).ortho hij, LinearMap.zero_apply,
    map_zero]

end Orthogonal
end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
end
