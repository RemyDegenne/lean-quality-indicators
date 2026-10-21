namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.UnitaryFinite

open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

lemma normalizedCoefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    inner ℂ (normalizedCoefficient a x₀ ha ρ w v) (normalizedCoefficient a x₀ ha ρ z t) =
      inner ℂ z w*inner ℂ v t := by
  let : Nonempty X := ⟨x₀⟩
  have hX : (Fintype.card X:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ)^2 =
      (Module.finrank ℂ V:ℂ)/(Fintype.card X:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    simp
  simp only [normalizedCoefficient,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [←mul_assoc,←pow_two,hs]
  have hi := coefficient_inner a x₀ ha ρ hρ w z hw hz v t
  field_simp
  simpa only [mul_assoc] using hi

end Thorp.UnitaryFinite
end ThorpNine.SparseSaving
end OAI
