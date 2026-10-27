public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
  CFSG.Quasithin.F53Mod Equiv

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_noncommuting_alt_five :
    ∃ a b : Perm (Fin 5), a ∈ alternatingGroup (Fin 5) ∧ b ∈ alternatingGroup (Fin 5) ∧
      a * b ≠ b * a :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 2 3,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel,
    by decide +kernel⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
end
