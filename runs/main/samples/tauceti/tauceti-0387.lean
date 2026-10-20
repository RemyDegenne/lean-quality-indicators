public section

open IsDedekindDomain Module NumberField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [NumberField F] (W : Affine F) [W.IsElliptic] [W.IsCharNeTwoNF]
  {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra F (Loc i)]

open scoped Classical in
theorem selmerGroup₂_le_selmerGroupA {S : Set (HeightOneSpectrum (𝓞 F))}
    (ha₂ : ∀ v ∉ S, v.valuation F W.a₂ ≤ 1) (ha₄ : ∀ v ∉ S, v.valuation F W.a₄ ≤ 1)
    (ha₆ : ∀ v ∉ S, v.valuation F W.a₆ ≤ 1)
    (hd : ∀ v ∉ S, WithZero.exp (-1) ≤ v.valuation F W.f.discr) :
    W.selmerGroup₂ (𝓞 F) Loc ≤ W.selmerGroupA (𝓞 F) S :=
  fun _ hm ↦ W.mem_selmerGroupA_of_forall_localRes fun v hv ↦
    W.range_μ_le_selmerGroupA_empty (ha₂ v hv) (ha₄ v hv) (ha₆ v hv) (hd v hv) <|
      (W.mem_localCondition_iff _).mp (((W.mem_selmerGroup₂_iff (𝓞 F) Loc).mp hm).2.1 v)

end WeierstrassCurve.Affine
end
