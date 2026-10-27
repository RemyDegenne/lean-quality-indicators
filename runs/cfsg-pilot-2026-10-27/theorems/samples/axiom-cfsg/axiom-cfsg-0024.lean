public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Basic

variable {X : Type} [Group X]

theorem IsDelta5Group.solvableRadical_eq [Finite X] (h : IsDelta5Group X) :
    CFSG.solvableRadical X = CFSG.pCore 2 X := by
  obtain ⟨α, β, hαs, hαk, -, -⟩ := h
  let e : (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := e.isSimpleGroup
  have hna : ∃ a b : X ⧸ CFSG.pCore 2 X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply not_solvable_alt5
    apply Group.isSolvable_of_comm
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hcon _ _
  exact A314.solvableRadical_eq_of_simple IsDelta5Group.solvable_pCore hs hna

end Basic
end CFSG.QuasithinUnique.A5.G3
end
