namespace OAI

namespace PeriodicLattice

local instance finiteFunctionEncodingRapidBounds {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace RapidCalculus

open Set Filter Topology TorusCalculus

open scoped ContDiff

theorem VectorAlgebra.mixed_bound {U : VectorField} (hU : VectorAlgebra U)
    (r J : ℕ) (α : MultiIndex) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ q : Torus, (1 + t) ^ J * ‖mixedD r α U t q‖ ≤ C := by
  have hsp (V : VectorField) (hV : VectorAlgebra V) (i : Fin 3) (k : ℕ) :
      VectorAlgebra ((spaceD i)^[k] V) := by
    induction k with
    | zero => exact hV
    | succ k ih => rw [Function.iterate_succ_apply']; exact ih.spaceDeriv i
  let V := (spaceD 2)^[α 2] ((spaceD 1)^[α 1] ((spaceD 0)^[α 0] U))
  have hV : VectorAlgebra V := hsp _ (hsp _ (hsp _ hU 0 _) 1 _) 2 _
  have htime : VectorAlgebra (fullTimeD^[r] V) := by
    induction r with
    | zero => exact hV
    | succ r ih => rw [Function.iterate_succ_apply']; exact ih.timeDeriv
  obtain ⟨C, hC⟩ := htime.bound J
  refine ⟨C, fun t ht q => ?_⟩
  change (1 + t) ^ J * ‖timeD^[r] V t q‖ ≤ C
  rw [iterate_timeD_eq_fullTimeD hV.smooth r t ht]
  exact hC t ht q

end RapidCalculus
end
end PeriodicLattice
end OAI
