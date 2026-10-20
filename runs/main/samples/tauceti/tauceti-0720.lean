public section

open Filter Topology

namespace TauCeti.Huber

theorem IsPseudoUniformizer.of_norm_lt_one {R : Type*} [SeminormedRing R] {ϖ : R}
    (hϖ : IsUnit ϖ) (hϖ1 : ‖ϖ‖ < 1) : IsPseudoUniformizer ϖ :=
  isPseudoUniformizer_iff.mpr ⟨hϖ, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1⟩

end TauCeti.Huber
end
