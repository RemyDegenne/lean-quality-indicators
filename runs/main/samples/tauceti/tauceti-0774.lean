public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped AdeleGaloisAction Pointwise TensorProduct

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.ideleMulDistribMulAction

variable {K L}

theorem ofFiniteIdele_map_finiteAdeleGaloisAction (σ : L ≃ₐ[K] L)
    (a : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    IdeleGroup.ofFiniteIdele (𝓞 L) L (Units.map (finiteAdeleGaloisAction K L σ : _ →* _) a) =
      σ • IdeleGroup.ofFiniteIdele (𝓞 L) L a := by
  refine Units.ext ?_
  rw [coe_idele_smul]
  refine Prod.ext ?_ ?_
  · rw [adeleGaloisAction_fst, IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_ofFiniteIdele]
    exact (map_one _).symm
  · rw [adeleGaloisAction_snd, IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_ofFiniteIdele,
      Units.coe_map, MonoidHom.coe_ofClass]

end TauCeti.GlobalNumberFields
end
end
