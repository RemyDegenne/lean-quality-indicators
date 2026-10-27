@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [Field R]

/-- An irreducible degree-two polynomial and a specified root in the quadratic
algebra determine an algebra equivalence over any base field. The image of the
adjoined root is exactly the specified root; no sign or normalization is
imposed. -/
noncomputable def adjoinRootEquivOfRoot (p : R[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : QuadraticAlgebra R (-1) 0)
    (hz : p.aeval z = 0) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom p (Algebra.ofId R _) z (by
      simpa only [Polynomial.aeval_def, Algebra.toRingHom_ofId] using hz)) (by
      let lift := AdjoinRoot.liftAlgHom p (Algebra.ofId R _) z (by
        simpa only [Polynomial.aeval_def, Algebra.toRingHom_ofId] using hz)
      change Function.Bijective lift
      have : Fact (Irreducible p) := ⟨hp⟩
      have : FiniteDimensional R (AdjoinRoot p) :=
        Module.Finite.of_basis (AdjoinRoot.powerBasis hp.ne_zero).basis
      have hfinrank : Module.finrank R (AdjoinRoot p) =
          Module.finrank R (QuadraticAlgebra R (-1) 0) := by
        calc
          _ = p.natDegree := finrank_quotient_span_eq_natDegree
          _ = 2 := hdeg
          _ = _ := (QuadraticAlgebra.finrank_eq_two (-1 : R) 0).symm
      have hinj : Function.Injective lift := RingHom.injective lift.toRingHom
      have hsurj : Function.Surjective lift.toLinearMap :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank
          (f := lift.toLinearMap)).mp (fun x y hxy =>
            hinj (by simpa only [AlgHom.toLinearMap_apply] using hxy))
      exact ⟨hinj, fun y => by
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨x, by simpa only [AlgHom.toLinearMap_apply] using hx⟩⟩)

end QuadraticAlgebra
end
end
