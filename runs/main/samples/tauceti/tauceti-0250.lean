public section

namespace TauCeti

@[simp] theorem cartanMatrix_D_graphPermD (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    (DynkinType.D n).cartanMatrix (graphPermD n (by omega) i) (graphPermD n (by omega) j) =
      (DynkinType.D n).cartanMatrix i j := by
  simp only [DynkinType.cartanMatrix_D, graphPermD]
  exact cartanMatrix_D_swap_fork n hn _ _ rfl rfl i j

end TauCeti
end
