public section

open Pointwise Topology TauCeti.Localization

namespace TauCeti.Huber

namespace PairOfDefinition

section Topological

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem locIdealImage_one_le_adjoin_plus (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locIdealImage P T s S 1 ≤
      (Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))).toSubring.toAddSubgroup := by
  set E := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))
  -- The span induction carries a `D`-coefficient `c` along, so that the `smul` step can move a
  -- fresh coefficient into it; every generator is absorbed by the previous theorem.
  have hJ : ∀ d ∈ locIdeal P T s S ^ 1, ∀ c : locSubring P T s S,
      ((c * d : locSubring P T s S) : S) ∈ E := by
    intro d hd
    rw [locIdeal_pow_eq_span, pow_one] at hd
    induction hd using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      intro c
      rw [MulMemClass.coe_mul, toLocSubring_apply]
      exact locSubring_mul_idealOfDefinition_mem_adjoin_plus P Aplus hIplus T s S c.2 hi
    | zero =>
      intro c
      rw [mul_zero, ZeroMemClass.coe_zero]
      exact zero_mem E
    | add y z _ _ hy hz =>
      intro c
      rw [mul_add, AddMemClass.coe_add]
      exact add_mem (hy c) (hz c)
    | smul r y _ hy =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (c * r)
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S 1).mp hx
  exact Subring.mem_toAddSubgroup.mpr (Subalgebra.mem_toSubring.mpr (one_mul d ▸ hJ d hd 1))

end Topological
end PairOfDefinition
end TauCeti.Huber
end
