public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable (L : IntegralLattice V) (ι : Type v) [Fintype ι]

/-- The coordinate power `L^ι` of an integral lattice: the orthogonal sum of `ι` copies of `L`,
with carrier the functions `ι → V` whose values all lie in `L`. -/
def coordinatePower : IntegralLattice (ι → V) where
  carrier := Submodule.pi Set.univ fun _ ↦ L.carrier
  form := coordinatePowerForm L ι
  isLattice := isLattice_pi L ι
  isSymm := ⟨fun x y ↦ by
    simp only [coordinatePowerForm_apply]
    exact Finset.sum_congr rfl fun i _ ↦ L.isSymm.eq (x i) (y i)⟩
  le_dual := by
    intro x hx
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [coordinatePowerForm_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      L.le_dual (hx i (Set.mem_univ i)) (y i) (hy i (Set.mem_univ i))

end TauCeti.IntegralLattice
end
