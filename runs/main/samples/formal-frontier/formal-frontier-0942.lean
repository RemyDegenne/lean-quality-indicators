@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem map_eq_smul_determinant (n : ℕ) [Module.Invertible R (⋀[R]^n M)]
    (f : Module.End R M) (x : ⋀[R]^n M) :
    map n f x = determinant R M n f • x := by
  let e := Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)
  change map n f x = e (e.symm (map n f)) x
  exact DFunLike.congr_fun (e.apply_symm_apply (map n f)).symm x

end exteriorPower
end
end
