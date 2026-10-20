public section

open Ideal Module

open TauCeti.RamificationInertia

namespace Ideal

theorem ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsPrime] :
    (P.primesOver S).ncard = finrank R S ↔
      ∀ Q ∈ P.primesOver S, Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by
  refine ⟨fun h Q ⟨_, _⟩ ↦
    ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank P Q h,
    fun h ↦ ?_⟩
  have := (Algebra.QuasiFinite.finite_primesOver (S := S) P).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank (p := P),
    Finset.sum_congr rfl fun q _ ↦ by rw [(h q.1 q.2).1, (h q.1 q.2).2, mul_one]]
  simp

end Ideal
end
