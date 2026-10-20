@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem primewisePadicProcyclicModel_exponents
    (e : Nat.Primes → ℕ∞)
    (h : IsProcyclic (primewisePadicProcyclicModel.{u} e)) :
    h.exponents = e := by
  rw [h.exponents_eq_of_generator _
    (primewisePadicRealizationGenerator_isTopologicalGenerator e),
    primewisePadicExponentsOfGenerator,
    primewisePadicMapOfRealizationGenerator,
    primewisePadicKernelExponents_realizationMap]

end ProfiniteGrp
end
