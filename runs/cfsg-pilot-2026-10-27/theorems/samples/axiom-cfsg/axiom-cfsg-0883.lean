public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open

open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.Quasithin.SteinbergCC (powOneClosure)

open scoped commutatorElement

section Plane

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem mem_pCore_of_mem_fitting {X : Type*} [Group X] [Finite X] {q : ℕ} [Fact q.Prime] {y : X}
    (hy : y ∈ CFSG.fittingSubgroup X) {k : ℕ} (hk : orderOf y = q ^ k) : y ∈ CFSG.pCore q X := by
  set F := CFSG.fittingSubgroup X
  have hk' : (⟨y, hy⟩ : F) ^ (q ^ k) = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
    exact pow_orderOf_eq_one y)
  have hpg : IsPGroup q (Subgroup.zpowers (⟨y, hy⟩ : F)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change ((⟨y, hy⟩ : F) ^ n) ^ (q ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hmem : y ∈ (P : Subgroup F).map F.subtype :=
    ⟨⟨y, hy⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  exact Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent q P hmem

end Plane
end CFSG.Quasithin.H13.NQRigid
end
