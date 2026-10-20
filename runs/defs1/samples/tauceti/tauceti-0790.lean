public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped TensorProduct

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]

variable {V : Type v} [AddCommGroup V] [Module K V]

variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Local representation of one quadratic form by another: `Q.LocallyRepresents R` holds when
every finite and real localization of `Q` admits an injective isometry into the corresponding
localization of `R`. -/
def LocallyRepresents (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K),
      (Q.atFinitePlace v).IsRepresentedBy (R.atFinitePlace v)) ∧
    ∀ w : {w : InfinitePlace K // w.IsReal},
      (Q.atRealPlace w).IsRepresentedBy (R.atRealPlace w)

end QuadraticForm
end
end
