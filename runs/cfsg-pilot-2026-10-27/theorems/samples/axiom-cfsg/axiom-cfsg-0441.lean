public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer

open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem nonempty_secK_pPrimeCore_equiv (hZ : center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥) :
    Nonempty (↥(h.secImage y h.K) ⧸ pPrimeCore 2 ↥(h.secImage y h.K) ≃*
      ↥h.K ⧸ pPrimeCore 2 ↥h.K) := by
  let e₁ : ↥(h.K.subgroupOf (h.secG0 y)) ≃* ↥h.K := subgroupOfEquivOfLe K_le_secG0
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hZ' : center (↥(h.K.subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥(h.K.subgroupOf (h.secG0 y))) = ⊥ :=
    B5a.center_eq_bot_of_equiv e₂.symm hZ
  obtain ⟨e₃⟩ := TwoQuot.nonempty_pPrimeCore_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y K_le_centralizer_secB0) (h.isPGroup_ker_secMk y) hZ'
  exact ⟨e₃.symm.trans e₂⟩

end Hyp52
end CFSG.ComponentClassification.GSThmB
end
