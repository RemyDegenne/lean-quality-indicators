set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalModN

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [IsTopologicalAddGroup C]

section CompactHausdorff

variable [CompactSpace A] [T2Space A]

/-- For a compact Hausdorff group, the closed quotient is continuously
additively equivalent to mathlib's algebraic `ModN`, equipped with its quotient
topology. -/
def compactModNEquiv (n : ℕ) : TopologicalModN A n ≃ₜ+ ModN A n := by
  let forward : TopologicalModN A n →ₜ+ ModN A n := compactToModN n
  let inverse : ModN A n →ₜ+ TopologicalModN A n :=
    algebraicToClosed n
  exact
    { toFun := forward
      invFun := inverse
      left_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        calc
          inverse (forward (mkQ n a)) = inverse (modNMk n a) :=
            congrArg inverse (compactToModN_mk n a)
          _ = mkQ n a := algebraicToClosed_mk n a
      right_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        calc
          forward (inverse (modNMk n a)) = forward (mkQ n a) :=
            congrArg forward (algebraicToClosed_mk n a)
          _ = modNMk n a := compactToModN_mk n a
      map_add' := forward.map_add
      continuous_toFun := forward.continuous
      continuous_invFun := inverse.continuous }

end CompactHausdorff
end TopologicalModN
end
end
