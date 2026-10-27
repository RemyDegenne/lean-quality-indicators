public section

namespace CFSG.AGLEmbeddingD2.HeisSymplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.CurtisTits
  CFSG.AGLEmbeddingD2.SquareSymplectic TauCeti.GLSymplecticFin CFSG.LieType.Steinberg

section C2

variable {n : ℕ} {F : Type} [Field F]

theorem elt_mem_coordFix {r : RootSubgroupIndex n} {S : Finset (Fin n ⊕ Fin n)}
    (h1 : (pos1 r).1 ∈ S ∧ (pos1 r).2 ∈ S) (h2 : (pos2 r).1 ∈ S ∧ (pos2 r).2 ∈ S) (c : F) :
    ((elt r c : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈ coordFix S := by
  intro x y hxy
  have hx1 : (x, y) ≠ pos1 r := fun h => by
    have hxe : x = (pos1 r).1 := congrArg Prod.fst h
    have hye : y = (pos1 r).2 := congrArg Prod.snd h
    rcases hxy with hx | hy
    · exact hx (by rw [hxe]; exact h1.1)
    · exact hy (by rw [hye]; exact h1.2)
  have hx2 : (x, y) ≠ pos2 r := fun h => by
    have hxe : x = (pos2 r).1 := congrArg Prod.fst h
    have hye : y = (pos2 r).2 := congrArg Prod.snd h
    rcases hxy with hx | hy
    · exact hx (by rw [hxe]; exact h2.1)
    · exact hy (by rw [hye]; exact h2.2)
  change mat n F (elt r c) x y = _
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, E_eq_zero r hx1 hx2, smul_zero, add_zero]

end C2
end CFSG.AGLEmbeddingD2.HeisSymplectic
end
