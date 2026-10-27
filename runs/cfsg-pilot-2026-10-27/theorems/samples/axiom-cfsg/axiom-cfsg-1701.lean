public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open scoped IsMulCommutative

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {A : Subgroup ↥(orthDerived Q)}

theorem isPlaneFrame_update_pow (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} (hc : ¬ p ∣ c) :
    IsPlaneFrame Q p U (Function.update ρ j (ρ j ^ c))
      (Subgroup.closure (Set.range (Function.update ρ j (ρ j ^ c)))) := by
  have hT := isPlaneFrame_update_pow_aux1 hp hF j hc
  have hord := isPlaneFrame_update_pow_aux2 hp hF j hc
  have hpp := isPlaneFrame_update_pow_aux3 hF j (c := c)
  have hmt := isPlaneFrame_update_pow_aux4 hF j (c := c)
  have hez := isPlaneFrame_update_pow_aux5 hp hF j hc
  refine
    { toIsPlaneSystem := hF.toIsPlaneSystem
      orderOf_eq := ?_
      apply_of_perp := ?_
      maps_to := ?_
      eq_zero_of_apply_eq := ?_
      isElemAbelian := ?_
      closure_eq := rfl }
  · intro k
    by_cases hk : k = j
    · rw [hk, Function.update_self]; exact hord
    · rw [Function.update_of_ne hk]; exact hF.orderOf_eq k
  · intro k x hx
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self]; exact hpp x hx
    · rw [Function.update_of_ne hk]; exact hF.apply_of_perp k x hx
  · intro k x hx
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self]; exact hmt x hx
    · rw [Function.update_of_ne hk]; exact hF.maps_to k x hx
  · intro k x hx hfix
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self] at hfix; exact hez x hx hfix
    · rw [Function.update_of_ne hk] at hfix; exact hF.eq_zero_of_apply_eq k x hx hfix
  · rw [hT]; exact hF.isElemAbelian

end CFSG.LocalAnalysis.GLTheoremA.T173M
end
