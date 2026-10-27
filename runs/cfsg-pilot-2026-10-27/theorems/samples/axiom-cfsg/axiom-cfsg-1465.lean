public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.Open

open scoped Matrix

variable {K X H : Type} [Field K] [AddCommGroup X] [Module K X] [Group H]

section Inv

variable {act : H →* (X ≃ₗ[K] X)}

variable [Fintype K] [DecidableEq K]

theorem exists_invSub_isCompl (W : Submodule K X) (p : X →+ X) (hpW : ∀ v, p v ∈ W)
    (hp : ∀ w ∈ W, p w = w) (hpact : ∀ h v, p (act h v) = act h (p v)) :
    ∃ W' : Submodule K X, IsInvSub act W' ∧ IsCompl W W' := by
  obtain ⟨pK, hpKW, hpK, hpKact⟩ :=
    exists_linear_proj W p hpW hp (fun h => ((act h : X ≃ₗ[K] X) : X →ₗ[K] X)) hpact
  let f : X →ₗ[K] W := pK.codRestrict W hpKW
  have hf : ∀ x : W, f x = x := fun x => Subtype.ext (hpK x x.2)
  refine ⟨LinearMap.ker f, fun h x hx => ?_, LinearMap.isCompl_of_proj hf⟩
  rw [LinearMap.mem_ker] at hx ⊢
  have hx' : pK x = 0 := congrArg Subtype.val hx
  refine Subtype.ext ?_
  show pK (act h x) = 0
  have := hpKact h x
  simp only [LinearEquiv.coe_coe] at this
  rw [this, hx', map_zero]

end Inv
end CFSG.RankThree.GF2n.Stroth80.S715L
end
