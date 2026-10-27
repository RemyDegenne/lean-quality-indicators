public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

variable {k : ℕ} {ε π : Bool} {c : Fin (k + 1) → ZMod 5}

theorem fiveLineStabHom_ker (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    (hS5 : ∀ g : GL (Fin (k + 1)) (ZMod 5),
      g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) ↔
        g ∈ fiveReflectionGroup k ε π ∧
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c) :
    (fiveLineStabHom k ε π c hc).ker =
      (Subgroup.closure (fiveReflectionsFixing k ε π c)).subgroupOf
        (fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine (hS5 g.1).mpr ⟨g.2.1, ?_⟩
    have hspec := fiveLineStabHom_spec k ε π c hc g
    rw [h] at hspec
    simpa using hspec
  · intro h
    apply fiveLineStab_smul_unique hc
    rw [← fiveLineStabHom_spec k ε π c hc g, closure_fiveReflectionsFixing_fixes k ε π h,
      Units.val_one, one_smul]

end CFSG.OddTranspositions.PartThree
end
