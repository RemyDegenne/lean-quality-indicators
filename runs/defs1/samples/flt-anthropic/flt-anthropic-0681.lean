set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

noncomputable section

open Polynomial IsLocalRing IsDedekindDomain

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

open scoped Valued WithZero

namespace AlgebraicCurve.Place

section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

variable (F)

variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

def kw_ffgc_completionTraceF' [FiniteDimensional F F'] : F' →ₗ[F] (W.restrict F).adicCompletion :=
  { toFun := fun g => kw_ffgc_completionTrace F W (algebraMap F' W.adicCompletion g)
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun c x => by
      simp only [Algebra.smul_def, map_mul, RingHom.id_apply,
        kw_ffgc_adicCompletionComap_algebraMap_algebraMap]
      rw [← Algebra.smul_def, LinearMap.map_smul, Algebra.smul_def]
      rfl }

end CompletionTrace
end AlgebraicCurve.Place
end
end
end
end
