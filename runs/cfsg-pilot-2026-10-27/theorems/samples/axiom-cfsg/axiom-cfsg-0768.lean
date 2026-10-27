public section

namespace CFSG.Quasithin

namespace A38

theorem isQuasisimple_map_oddCore {X : Type*} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hL : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L)) :
    CFSG.IsQuasisimple ↥(L.map (QuotientGroup.mk' (CFSG.oddCore X))) := by
  let ρ : X →* X ⧸ CFSG.oddCore X := QuotientGroup.mk' (CFSG.oddCore X)
  let φ : ↥L →* ↥(L.map ρ) := ρ.subgroupMap L
  have hφ : Function.Surjective φ := ρ.subgroupMap_surjective L
  have hker : φ.ker = CFSG.oddCore ↥L := by
    rw [← oddCore_subgroupOf_of_normal L]
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ρ (x : X) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr h
  let e : (↥L ⧸ φ.ker) ≃* ↥(L.map ρ) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have e2 : (↥L ⧸ CFSG.oddCore ↥L) ≃* (↥L ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e2.trans e) hL

end A38
end CFSG.Quasithin
end
