open scoped Pointwise

open MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*}

noncomputable section

namespace PresentationOfFreeCotangent

variable {ι : Type*} (P : Generators R S ι) {σ : Type*}
  (b : Module.Basis σ S P.toExtension.Cotangent)

namespace Aux

variable {P} {b}

variable (D : Aux P b)

open scoped Classical in
/-- The "naive" presentation of `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` over `R`.
We make sure the section `T → R[X₁, ..., Xₙ]` maps `-1` to `-1` and `0` to `0`. -/
def presLeft : Presentation R D.T ι σ :=
  .naive (fun x ↦ if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x ↦ by
    split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

end Aux
end PresentationOfFreeCotangent
end
end Algebra.Generators
