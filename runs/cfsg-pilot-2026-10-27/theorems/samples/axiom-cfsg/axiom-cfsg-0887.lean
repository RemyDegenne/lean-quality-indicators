public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem mem_centralizer_fourV {x : G} :
    x ∈ Subgroup.centralizer (fourV φ : Set G) ↔ IsTorus φ x := by
  rw [fourV, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h J (Set.mem_insert _ _), h _ (Set.mem_insert_of_mem _ rfl)⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases hy with hy | hy
    · rw [hy]; exact h1
    · rw [Set.mem_singleton_iff.mp hy]; exact h2

end CFSG.BrauerLinearThree
end
