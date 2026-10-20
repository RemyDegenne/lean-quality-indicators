open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

/-- The signed integral coefficient of three basis vectors in the natural, odd half-spin, and
even half-spin blocks. The absolute value stored in the table selects the third basis vector;
its sign is the coefficient. -/
def trialityCoefficient (a : Block 0) (b : Block 1) (c : Block 2) : ℤ :=
  let table : Fin 8 → Fin 8 → ℤ := ![
    ![0, 0, 0, -8, 0, 7, -6, 4],
    ![0, 0, 8, 0, -7, 0, 5, -3],
    ![0, -8, 0, 0, 6, -5, 0, 2],
    ![8, 0, 0, 0, -4, 3, -2, 0],
    ![0, 7, -6, 5, 0, 0, 0, -1],
    ![-7, 0, 4, -3, 0, 0, 1, 0],
    ![6, -4, 0, 2, 0, -1, 0, 0],
    ![-5, 3, -2, 0, 1, 0, 0, 0]]
  let localIndex {j : Fin 3} (x : Block j) : Fin 8 :=
    ⟨x.1.val % 8, Nat.mod_lt _ (by omega)⟩
  let q := table (localIndex a) (localIndex b)
  if q.natAbs = (localIndex c).val + 1 then q.sign else 0

end TauCeti.D4Tripled
end
