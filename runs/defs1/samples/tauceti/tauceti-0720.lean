public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {ι : Type*} {L : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

variable (m : ℕ)

/-- **The Selmer structure of the `m`-Selmer group**: on `E(Kˢ)[m]`, localised along the
restriction maps `τ i`, with local condition at `L i` the kernel of
`H¹(G_{L i}, E[m]) → H¹(G_{L i}, E)`. When `W` is elliptic and `m` is invertible in `K`, this
kernel is the image of the local Kummer map `E(L i) → H¹(G_{L i}, E[m])`
(`WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`). -/
def selmerStructure :
    SelmerStructure (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
      (fun i => AbsoluteGaloisGroup (L i)) (fun i => (W⁄(L i)).TorsionCoeff m) where
  groupHom i := absoluteGaloisGroupMap (τ i)
  coeffHom i := W.torsionCoeffBaseChange (τ i) m
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i := W.torsionCoeffBaseChange_smul (τ i) m
  localCondition i :=
    (explicitCoeff1 _ _ ((W⁄(L i)).torsionCoeffIncl m) continuous_of_discreteTopology).ker

end WeierstrassCurve
end
end
