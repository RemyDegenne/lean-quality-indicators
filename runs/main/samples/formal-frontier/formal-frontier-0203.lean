@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem primewisePadicKernelExponents_realizationMap (e : Nat.Primes → ℕ∞) :
    primewisePadicKernelExponents (primewisePadicRealizationMap.{u} e) = e := by
  rw [primewisePadicKernelExponents, primewisePadicKernelIdeal_realizationMap,
    primewisePadicIdealExponents_idealOfExponents]

end ProfiniteGrp
end
