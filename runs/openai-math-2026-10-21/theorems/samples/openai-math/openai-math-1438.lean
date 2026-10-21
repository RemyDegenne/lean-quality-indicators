namespace OAI

section

namespace KLInvariance.ReflectionFrobenius

universe uk ua uv

variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]

noncomputable section

variable (τ : A ≃ₐ[k] A) (α : A)

variable (hinv : Function.Involutive τ) (hα : α ≠ 0) (hanti : τ α = -α)
  (hdiv : ∀ a : A, α ∣ a - τ a)

section Symmetric

variable {V : Type uv} [AddCommGroup V] [Module k V]

omit [CharZero k] in
 theorem symmetricMap_comp (e d : V ≃ₗ[k] V) :
    (symmetricMap d).comp (symmetricMap e) = symmetricMap (e.trans d) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

end Symmetric
end
end KLInvariance.ReflectionFrobenius
end
end OAI
