public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G]

section Coord

variable {V : Subgroup G} {ι : Type} {F : Type} [Field F]
  (β : ↥V →* Multiplicative (Fin 1 → ι → F))

variable {β}

theorem IsCoordAct.inv [Fintype ι] [DecidableEq ι] {g : G} {A : GL ι F}
    (hA : IsCoordAct β g (A : Matrix ι ι F).mulVec) :
    IsCoordAct β g⁻¹ ((A⁻¹ : GL ι F) : Matrix ι ι F).mulVec := by
  intro u v huv
  have huv' : (u : G) = g * v * g⁻¹ := by rw [huv]; group
  rw [hA v u huv', Matrix.mulVec_mulVec]
  simp

end Coord
end CFSG.Quasithin.MS93
end
