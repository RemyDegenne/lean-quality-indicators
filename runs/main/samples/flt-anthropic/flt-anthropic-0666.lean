namespace P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 6400000

set_option maxHeartbeats 12800000

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

set_option maxHeartbeats 1600000

namespace FLT

namespace Gapsw7X3xCrossPlaceTraceDecomposition

p2m_open_scoped

open FLT.Gapsw7X1mCompletionCarrier

open FLT.Gapsw7X3jCarrierAlgebraWiring

open FLT.Gapsw7X3mCompletionFieldFiniteDimensional

theorem gapsw7_x3x_trace_decomposition_of_prod_iso (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b)
      = ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  have _em := Classical.em
  rw [← gapsw7_x3x_trace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b),
    gapsw7_x3x_trace_pi A S]

end Gapsw7X3xCrossPlaceTraceDecomposition
end FLT
end
end
end
end
end
end
end P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
