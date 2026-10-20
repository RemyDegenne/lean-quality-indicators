public section

noncomputable section

open IsDedekindDomain NumberField Module

open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

variable {L v}

variable (L v)

/-- **The semi-local decomposition** `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`: completing `L` at the
finitely many places above a finite place `v` of `K` decomposes the scalar extension of `L` to
`K_v` into the product of those completions. -/
def semilocalEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (semilocalHom L v)
    -- The `show` is load-bearing. `Function.Bijective` is semireducible, so the bare anonymous
    -- constructor elaborates at the unfolded conjunction instead, and the resulting
    -- `AlgEquiv.ofBijective` term is then not type-correct at `instances` transparency: `simp`
    -- refuses to rewrite it with `AlgEquiv.coe_ofBijective`, which is what proves
    -- `semilocalEquiv_tmul` below.
    (show Function.Bijective (semilocalHom L v) from
      ⟨semilocalHom_injective L v, semilocalHom_surjective L v⟩)

end TauCeti
end
end
