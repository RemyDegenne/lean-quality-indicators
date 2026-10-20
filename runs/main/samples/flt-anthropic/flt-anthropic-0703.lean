namespace P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_open

open scoped TensorProduct

open scoped TensorProduct.RightActions

p2m_reactivate

namespace FDTEF

section ProductData

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
theorem isRegularSemisimple_map_iff_of_injective_isUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : ∀ x : R, IsUnit (f x) → IsUnit x) (g : GL (Fin 2) R) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) ↔ IsRegularSemisimple g := by
  unfold IsRegularSemisimple
  rw [disc_map]
  exact ⟨hf _, fun h => h.map f⟩

end ProductData
end FDTEF
end P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar
