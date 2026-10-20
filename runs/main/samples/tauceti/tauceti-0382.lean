public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology

variable (K : Type) [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))

theorem ideleSumLocalInv_eq_sum (x : L.H (ideleFormation K) 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : ideleSupport K L x ⊆ S) :
    ideleSumLocalInv K L x =
      ∑ v ∈ S, ideleLocalInvAt K L v x + ∑ w, ideleInfiniteInvAt K L w x := by
  rw [ideleSumLocalInv_apply, sumLocalInv_eq_sum K _ fun v hv ↦ by
    rw [ideleLocalization_fst_apply, ← ideleLocalInvAt_eq_zero_iff]
    exact ideleLocalInvAt_eq_zero_of_notMem_ideleSupport K L fun h ↦ hv (hS h)]
  simp only [ideleLocalization_fst_apply, ideleLocalization_snd_apply, ideleLocalInvAt_apply,
    ideleInfiniteInvAt_apply]

end TauCeti.ClassFieldTheory
end
end
