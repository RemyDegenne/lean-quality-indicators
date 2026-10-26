/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.Algebra.Algebra.Prod
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import MinimalPrimes.RingTheory.KrullDimension.Integral

/-!
# Krull dimension after extending the field of scalars

For a finite-type commutative algebra `A` over a field `K` and any field
extension `L/K`, scalar extension preserves Krull dimension. The tensor factors
are ordered as `A ⊗[K] L`, and `K`, `L` and `A` may lie in independent universes.
The algebra `A` can be zero, nonreduced, or not a domain, and `L/K` need not be
algebraic. Dimension takes values in `WithBot ℕ∞`; the zero ring has dimension `⊥`.

The private constructions use polynomial algebras over an arbitrary field,
the rational function extension, the quotient by the unit ideal, and a product
of two copies of the field. The product has zero divisors; it is not an example
of a nonreduced algebra.

## Proof

For a nontrivial finite-type algebra, Noether normalization gives a finite
injective map from a polynomial algebra. Its scalar extension is finite and
remains injective by flatness over the field. Integral injections preserve
Krull dimension before and after scalar extension, while polynomial base change
and the polynomial dimension formula identify both dimensions. The zero algebra
is handled separately using its dimension `⊥`.

## References and credit

The mathematical question arises in the context of J. S. Milne's *Abelian
Varieties*. The proof uses Noether normalization, as in the Stacks Project,
[Tag 00OW](https://stacks.math.columbia.edu/tag/00OW), and the integral comparison
`RingHom.IsIntegral.ringKrullDim_eq` from this library.

The constructions and laws use Mathlib. Credit for the dimension APIs goes to
Fangming Li, Jujian Zhang, Jingting Wang, Sihan Su, Yi Song and Christian Merten;
for multivariate polynomials to Johannes Hölzl, Johan Commelin and Mario Carneiro;
for finite-type algebras to Johan Commelin; for rational functions to Anne Baanen,
María Inés de Frutos-Fernández and Filippo A. E. Nuccio; for quotient rings to
Kenny Lau, Chris Hughes, Mario Carneiro and Anne Baanen; for product algebras to
Kenny Lau and Yury Kudryashov; for tensor algebras to Kim Morrison and
Johan Commelin; for polynomial tensor equivalences to Antoine Chambert-Loir;
for Noether normalization to Riccardo Brasca, Sihan Su, Wan Lin and Xiaoyang Su;
for flatness to Johan Commelin, Jujian Zhang and Yongle Hu; and for vector-space
bases to Johannes Hölzl, Mario Carneiro and Alexander Bentkamp. The normalization
formalization cites the Stacks Project, Tag 00OW. This file was developed with
AI assistance.

## License

The Mathlib sources are licensed under Apache-2.0, as is this module.
-/

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Extending the field of scalars preserves the Krull dimension of a finite-type
commutative algebra. No nontriviality assumption on the algebra and no
algebraicity assumption on the field extension are required. The proof uses
Mathlib's Noether normalization theorem (Stacks Project, Tag 00OW) and
`RingHom.IsIntegral.ringKrullDim_eq`. -/
public theorem ringKrullDim_tensorProduct_of_finiteType
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [FiniteType K A] :
    ringKrullDim (A ⊗[K] L) = ringKrullDim A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let : Subsingleton A := hA
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · let : Nontrivial A := hA
    obtain ⟨n, f, hf_inj, hf_fin⟩ := exists_finite_inj_algHom_of_fg K A
    let fL : MvPolynomial (Fin n) K ⊗[K] L →ₐ[K] A ⊗[K] L :=
      TensorProduct.map f (AlgHom.id K L)
    -- Finiteness and injectivity concern the same base extension of f.
    have hfL_fin : fL.toRingHom.Finite :=
      RingHom.Finite.tensorProductMap hf_fin (AlgHom.Finite.id K L)
    have hfL_inj : Function.Injective fL :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) f.toLinearMap hf_inj
    have hdim : ringKrullDim (MvPolynomial (Fin n) K) = ringKrullDim A :=
      (RingHom.Finite.to_isIntegral hf_fin).ringKrullDim_eq hf_inj
    have hdimL : ringKrullDim (MvPolynomial (Fin n) K ⊗[K] L) =
        ringKrullDim (A ⊗[K] L) :=
      hfL_fin.to_isIntegral.ringKrullDim_eq hfL_inj
    calc
      ringKrullDim (A ⊗[K] L) = ringKrullDim (MvPolynomial (Fin n) K ⊗[K] L) :=
        hdimL.symm
      _ = ringKrullDim (L ⊗[K] MvPolynomial (Fin n) K) :=
        ringKrullDim_eq_of_ringEquiv (TensorProduct.comm K _ _).toRingEquiv
      _ = ringKrullDim (MvPolynomial (Fin n) L) :=
        ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv
      _ = (n : WithBot ℕ∞) := by
        simpa only [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
          Fintype.card_fin, zero_add] using
          (MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := L) (ι := Fin n))
      _ = ringKrullDim (MvPolynomial (Fin n) K) := by
        symm
        simpa only [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
          Fintype.card_fin, zero_add] using
          (MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin n))
      _ = ringKrullDim A := hdim

end Algebra

noncomputable section

section PolynomialAlgebras

variable (K : Type u) [Field K]

-- RatFunc K carries its canonical field structure and polynomial-induced K-algebra.
private def rationalFunctionVariable : RatFunc K := RatFunc.X

private theorem rationalFunctionVariable_transcendental :
    Transcendental K (rationalFunctionVariable K) :=
  RatFunc.transcendental_X

-- Fin (n + 1) is inhabited, so this produces a polynomial variable, not a constant.
private def polynomialVariable (n : ℕ) : MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.X 0

private theorem polynomialVariable_ne_zero (n : ℕ) : polynomialVariable K n ≠ 0 :=
  MvPolynomial.X_ne_zero 0

-- FiniteType.lean supplies the finite-variable instance, starting from
-- Module.Finite.self and Module.Finite.finiteType for the self-algebra K/K.
private theorem polynomial_finiteType (n : ℕ) :
    Algebra.FiniteType K (MvPolynomial (Fin n) K) := inferInstance

-- The polynomial dimension formula computes dimension before scalar extension.
-- It includes the zero-variable boundary n = 0 and positive dimensions n + 1.
private theorem polynomial_ringKrullDim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞) := by
  simpa only [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add] using
    (MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin n))

-- Polynomial algebras retain their dimension over the rational function extension.
private theorem polynomial_tensorProduct_ringKrullDim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) K ⊗[K] RatFunc K) = (n : WithBot ℕ∞) :=
  (Algebra.ringKrullDim_tensorProduct_of_finiteType K (RatFunc K)
    (MvPolynomial (Fin n) K)).trans (polynomial_ringKrullDim K n)

end PolynomialAlgebras

section QuotientByTheUnitIdeal

variable (K : Type u) [Field K]

private def quotientTopProjection : K →ₐ[K] K ⧸ (⊤ : Ideal K) :=
  Ideal.Quotient.mkₐ K ⊤

private theorem quotientTop_subsingleton : Subsingleton (K ⧸ (⊤ : Ideal K)) :=
  Ideal.Quotient.subsingleton_iff.mpr rfl

-- Ideal.Quotient.Basic supplies Unique for the quotient by the unit ideal.
private theorem quotientTopProjection_eq_zero (k : K) :
    quotientTopProjection K k = 0 :=
  Subsingleton.elim _ _

-- The quotient algebra and finite-type instances are the canonical ones from
-- Ideal.Quotient.Operations and Algebra.FiniteType.quotient, respectively.
private theorem quotientTop_finiteType :
    Algebra.FiniteType K (K ⧸ (⊤ : Ideal K)) := inferInstance

-- TensorProduct.uniqueLeft uses the same quotient carrier and its subsingleton instance.
private theorem quotientTopTensor_subsingleton :
    Subsingleton ((K ⧸ (⊤ : Ideal K)) ⊗[K] RatFunc K) := inferInstance

-- Both the unit-ideal quotient and its scalar extension have dimension ⊥, not 0.
private theorem quotientTop_tensorProduct_ringKrullDim :
    ringKrullDim ((K ⧸ (⊤ : Ideal K)) ⊗[K] RatFunc K) =
      ringKrullDim (K ⧸ (⊤ : Ideal K)) :=
  Algebra.ringKrullDim_tensorProduct_of_finiteType K (RatFunc K) (K ⧸ (⊤ : Ideal K))

end QuotientByTheUnitIdeal

section ProductAlgebras

variable (K : Type u) [Field K]

private def firstFactorIdempotent : K × K := (1, 0)

private def secondFactorIdempotent : K × K := (0, 1)

private theorem product_algebraMap (k : K) : algebraMap K (K × K) k = (k, k) := by
  simp only [Prod.algebraMap_apply, Algebra.algebraMap_self_apply]

private theorem firstFactorIdempotent_ne_zero : firstFactorIdempotent K ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

private theorem secondFactorIdempotent_ne_zero : secondFactorIdempotent K ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Prod.snd h)

private theorem factorIdempotents_mul :
    firstFactorIdempotent K * secondFactorIdempotent K = 0 := by
  ext <;> simp [firstFactorIdempotent, secondFactorIdempotent]

private theorem firstFactorIdempotent_sq :
    firstFactorIdempotent K * firstFactorIdempotent K = firstFactorIdempotent K := by
  ext <;> simp [firstFactorIdempotent]

-- Prod.algebra gives diagonal scalars, and Algebra.FiniteType.prod applies
-- to the two canonical self-algebras of K.
private theorem product_finiteType : Algebra.FiniteType K (K × K) := inferInstance

-- The diagonal product algebra retains its dimension after scalar extension.
private theorem product_tensorProduct_ringKrullDim :
    ringKrullDim ((K × K) ⊗[K] RatFunc K) = ringKrullDim (K × K) :=
  Algebra.ringKrullDim_tensorProduct_of_finiteType K (RatFunc K) (K × K)

end ProductAlgebras
