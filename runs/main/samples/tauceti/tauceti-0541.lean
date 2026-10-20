public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open NumberField.mixedEmbedding.fundamentalCone TauCeti.NumberField.mixedEmbedding

open NumberField.Units

open scoped Pointwise Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
theorem measureReal_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
        (2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * regulator K) / 2 ^ 𝔪.infinitePart.card := by
  rw [eq_div_iff (by positivity), mul_comm, measureReal_def]
  simpa [volume_normLeOne, (regulator_pos K).le] using
    congrArg ENNReal.toReal (two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne 𝔪)

end TauCeti.GlobalNumberFields
end
