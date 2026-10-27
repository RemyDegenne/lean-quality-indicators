@[expose] public section

section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]

variable [Algebra R A] [Algebra R B] (I : Ideal B)

variable [Algebra A B]

variable (hI : I ^ 2 = ⊥)

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`,
there is a 1-1 correspondence between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps!]
def derivationToSquareZeroEquivLift [IsScalarTower R A B] : Derivation R A I ≃
    { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } := by
  refine ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, ?_⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 :), ?_, ?_⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel_right (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)

end ToSquareZero
end
