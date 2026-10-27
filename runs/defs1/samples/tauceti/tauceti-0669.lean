public section

namespace TauCeti.ContCohomology

universe u v w

open CategoryTheory _root_.groupCohomology

section NumeratorDegree0

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- Degree `0`, on the carriers: the explicit `H⁰(G, M) = M^G` is the submodule of invariants of
the induced representation. -/
def H0AddEquivInvariants : H0 G M ≃+ (Rep.ofDistribMulAction ℤ G M).ρ.invariants where
  toFun m := ⟨m.1, (mem_invariants_iff_mem_H0 m.1).2 m.2⟩
  invFun m := ⟨m.1, (mem_invariants_iff_mem_H0 (G := G) (M := M) m.1).1 m.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end NumeratorDegree0
end TauCeti.ContCohomology
end
