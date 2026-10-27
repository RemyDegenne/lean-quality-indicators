set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalPowerQuotient

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [CommGroup A] [CommGroup B] [CommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]

/-- A continuous multiplicative equivalence induces an equivalence of closed
power quotients. -/
def congr (n : ℕ) (e : A ≃ₜ* B) :
    TopologicalPowerQuotient A n ≃ₜ* TopologicalPowerQuotient B n := by
  let ef : A →ₜ* B :=
    { toMonoidHom := e.toMonoidHom
      continuous_toFun := e.continuous }
  let einf : B →ₜ* A :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := e.symm.continuous }
  exact
    { toFun := map n ef
      invFun := map n einf
      left_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        change map n einf (map n ef (mkQ n a)) = mkQ n a
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.symm_apply_apply a)
      right_inv := fun x ↦ by
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
        change map n ef (map n einf (mkQ n b)) = mkQ n b
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.apply_symm_apply b)
      map_mul' := (map n ef).map_mul
      continuous_toFun := (map n ef).continuous
      continuous_invFun := (map n einf).continuous }

end TopologicalPowerQuotient
end
end
