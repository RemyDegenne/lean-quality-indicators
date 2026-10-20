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

/-- The algebraic quotient maps continuously to the closed quotient for every
topological additive commutative group.  It is generally a further quotient,
not an equivalence. -/
def algebraicToClosed (n : ℕ) : ModN A n →ₜ+ TopologicalModN A n := by
  let H := (LinearMap.range (LinearMap.lsmul ℤ A n)).toAddSubgroup
  have hH : H ≤ (mkQ n).ker := by
    rintro x ⟨a, rfl⟩
    change mkQ n ((LinearMap.lsmul ℤ A n) a) = 0
    apply (QuotientAddGroup.eq_zero_iff
      ((LinearMap.lsmul ℤ A n) a)).mpr
    simpa using (nsmul_mem_closedMultiples (A := A) n a)
  let hom : ModN A n →+ TopologicalModN A n :=
    QuotientAddGroup.lift H (mkQ (A := A) n).toAddMonoidHom hH
  exact
    { toAddMonoidHom := hom
      continuous_toFun := by
        change Continuous hom
        rw [continuous_iff_coinduced_le]
        unfold instTopologicalSpaceModN
        rw [coinduced_compose]
        rw [show (hom : ModN A n → TopologicalModN A n) ∘
            (ModN.mkQ n : A → ModN A n) =
            (mkQ n : A → TopologicalModN A n) by
          funext a
          rfl]
        exact continuous_iff_coinduced_le.mp (mkQ n).continuous }

end TopologicalModN
end
end
