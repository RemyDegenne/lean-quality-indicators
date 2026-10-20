namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace R4CompField

section Subst

variable {d : ℕ} {B : Type u} [CommRing B]

variable {χ : Fin d → MvPowerSeries (Fin d) B}

variable {b : ℕ} {ε : Fin b → MvPowerSeries (Fin d) B}

theorem mul_Theta_eq (hχ : ∀ i, constantCoeff (χ i) = 0) (a : MvPowerSeries (Fin d) B)
    (v : Fin b → Fin b → MvPowerSeries (Fin d) B) (hv : ∀ i, a * ε i = Theta χ ε (v i))
    (c : Fin b → MvPowerSeries (Fin d) B) :
    a * Theta χ ε c = Theta χ ε (fun k => ∑ i, c i * v i k) := by
  calc a * Theta χ ε c = ∑ i, subst χ (c i) * (a * ε i) := by
          rw [Theta, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, subst χ (c i) * Theta χ ε (v i) := Finset.sum_congr rfl fun i _ => by rw [hv i]
    _ = ∑ i, Theta χ ε (fun k => c i * v i k) :=
          Finset.sum_congr rfl fun i _ => by rw [Theta_mul_left hχ]
    _ = Theta χ ε (∑ i, fun k => c i * v i k) := (Theta_finset_sum hχ _ _).symm
    _ = Theta χ ε (fun k => ∑ i, c i * v i k) := by
          congr 1
          funext k
          rw [Finset.sum_apply]

end Subst
end R4CompField
end
end P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
