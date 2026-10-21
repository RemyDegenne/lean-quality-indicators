namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

section

section

open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem mixed_derivation_pow_add {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (D : Fin 3 → Derivation R A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (a b : Fin 3 → ℕ) (x : A) :
    ((D 0).toLinearMap ^ (a 0 + b 0))
      (((D 1).toLinearMap ^ (a 1 + b 1)) (((D 2).toLinearMap ^ (a 2 + b 2)) x)) =
      ((D 0).toLinearMap ^ a 0) (((D 1).toLinearMap ^ a 1) (((D 2).toLinearMap ^ a 2)
        (((D 0).toLinearMap ^ b 0) (((D 1).toLinearMap ^ b 1)
          (((D 2).toLinearMap ^ b 2) x))))) := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using mixed_iterate_add
    (fun i => (D i : A → A)) h01 h02 h12 a b x

end WeightedTorusJets.Geometry
end
end
end Erdos970
end OAI
