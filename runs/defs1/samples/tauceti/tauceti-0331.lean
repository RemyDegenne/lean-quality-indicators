public section

namespace TauCeti

universe u v

variable {p : ℕ} {X : Type u}

namespace freeProP

section FinSucc

variable {n : ℕ}

/-- **Extension of an automorphism along `Fin.succ`.** For a continuous automorphism `e` of the
free pro-`p` group on `Fin n`, the continuous automorphism of the free pro-`p` group on
`Fin (n + 1)` fixing the first generator `x₀` and acting on the remaining generators
`x_{j+1}`, `j : Fin n`, through `e`, read in `freeProP p (Fin (n + 1))` along
`freeProP.map Fin.succ` (`TauCeti.freeProP.finSuccExtend_map_succ`). Its inverse is the extension
of `e.symm`. -/
noncomputable def finSuccExtend (e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n)) :
    freeProP p (Fin (n + 1)) ≃ₜ* freeProP p (Fin (n + 1)) where
  toFun := lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e (of j)))
  invFun := lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e.symm (of j)))
  left_inv y := by
    have h := lift_cons_comp_lift_cons (p := p) (e.symm : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
    simp only [ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply, lift_cons_id] at h
    simpa using DFunLike.congr_fun h y
  right_inv y := by
    have h := lift_cons_comp_lift_cons (p := p) (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      (e.symm : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
    simp only [ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.apply_symm_apply, lift_cons_id] at h
    simpa using DFunLike.congr_fun h y
  map_mul' := map_mul _
  continuous_toFun := (lift _ _).continuous
  continuous_invFun := (lift _ _).continuous

end FinSucc
end freeProP
end TauCeti
end
