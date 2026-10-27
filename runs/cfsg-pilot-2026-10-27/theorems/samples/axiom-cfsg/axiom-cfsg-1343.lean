public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

open scoped commutatorElement

namespace TypeUnique

variable {H H' : Type} [Group H] [Group H'] {S : LeechTypeSystem H} {S' : LeechTypeSystem H'}

namespace Glue

variable (G : Glue S S')

theorem ζ_orderOf : orderOf G.ζ = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have e : (⟨(S.z, 1), G.z1_mem_P⟩ * ⟨(S.z, 1), G.z1_mem_P⟩ : ↥G.P) = 1 :=
      Subtype.ext (by simp [S.z_mul_self])
    show (QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ : G.Cover) ^ 2 = 1
    rw [pow_two, ← QuotientGroup.mk_mul, e]
    rfl
  · intro h
    exact G.z1_not_mem_Δ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))

end Glue
end TypeUnique
end CFSG.Monster.GMS
end
