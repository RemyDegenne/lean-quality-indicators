public noncomputable section

open IsDedekindDomain NumberField CategoryTheory

open IsDedekindDomain.HeightOneSpectrum

open scoped NumberField AdicCompletionExtension Pointwise TensorProduct WithZero

namespace TauCeti

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The units of `K_v ⊗[K] L` whose components belong to the integer-unit groups
of every completion above `v`. -/
def semilocalIntegralUnits (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K ⊗[K] L)ˣ :=
  ⨅ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
    (unitFiltration (w.1.adicCompletion L) 0).comap
      (Units.map ((Pi.evalMonoidHom (fun w' :
        {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} ↦
          w'.1.adicCompletion L) w).comp (semilocalEquiv L v : _ →* _)))

end TauCeti
end
