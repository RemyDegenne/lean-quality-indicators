public section

namespace TauCeti.ContCohomology

universe u v

section DegreeZero

variable {G : Type u} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable [ContinuousMul G]

variable (G U A) in
/-- **Shapiro's lemma in degree zero**, `H⁰(G, Coind_U^G A) ≅ H⁰(U, A)`, by evaluation at `1`.

A `G`-invariant element of the coinduced module is constant and the constant it takes is
`U`-invariant; conversely a `U`-invariant `a : A` is `TauCeti.ContCohomology.constCoind`. Only
continuity of the multiplication on `G` is used: neither compactness of `G` nor closedness of `U`
enters in this degree. -/
def explicitShapiro0 : H0 G (DiscreteCoind G U A) ≃+ H0 U A where
  toFun f := ⟨(f : DiscreteCoind G U A) 1, (FixedPoints.mem_addSubgroup U A _).2 fun u => by
    rw [← DiscreteCoind.apply_coe, apply_eq_apply_one_of_mem_H0 f]⟩
  invFun a := ⟨constCoind G a, constCoind_mem_H0 a⟩
  left_inv f := Subtype.ext (DiscreteCoind.ext fun g => by
    rw [constCoind_apply, apply_eq_apply_one_of_mem_H0 f])
  right_inv a := Subtype.ext (constCoind_apply a 1)
  map_add' _ _ := (rfl)

end DegreeZero
end TauCeti.ContCohomology
end
