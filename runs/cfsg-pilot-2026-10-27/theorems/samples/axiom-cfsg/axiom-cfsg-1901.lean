public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T CFSG.ClassicalInvolution.Q3.TL4
  QuadraticMap

open CFSG.LieType.Universal.Spin (spinAction quadPlus nondegenerate_quadPlus)

open CFSG.Open (StatedProj StatedOmega StatedQuadPlus)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Q₀" => quadPlus 4 (ZMod 3)

local notation "Proj₈" => StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))

theorem fk_congr_descAut_conj {e : Proj₈ ≃* omegaProj (nondegenerate_quadPlus 4 (ZMod 3))}
    (α : MulAut (spinGroup Q₄)) (y : spinGroup Q₄)
    (hαy : ∀ x, spinAction Q₄ (α x) = spinAction Q₄ y * spinAction Q₄ x * (spinAction Q₄ y)⁻¹) :
    MulAut.congr e (Q3MFOD.descAut α) = MulAut.conj (e (d4Proj (GaloisField 3 1) y)) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨p, rfl⟩ := e.surjective z
  obtain ⟨x, rfl⟩ := Q3MFOD.d4Proj_surjective p
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    Q3MFOD.descAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  exact d4Proj_eq_of_spinAction_eq (by rw [hαy, map_mul, map_mul, map_inv])

end CFSG.OddStandard.SmallF3.Omega
end
