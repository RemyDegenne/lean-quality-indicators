@[expose] public section

open TensorProduct Matrix

open scoped TensorProduct BigOperators Kronecker Matrix

variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]
  {p₂ : Type*} [Fintype p₂] [DecidableEq p₂] {n₂ : p₂ → Type*} [∀ i, Fintype (n₂ i)]
  [∀ i, DecidableEq (n₂ i)]

local notation "ℍ" => PiMat ℂ p n

local notation "ℍ₂" => PiMat ℂ p₂ n₂

local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : Π i : p, Module.Dual ℂ (Matrix (n i) (n i) ℂ)} {ψ : Π i,
  Module.Dual ℂ (Matrix (n₂ i) (n₂ i) ℂ)}

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ ℍ ℍ ℍ)

local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ ℍ ℍ ℍ))

local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ ℍ ℂ))

local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ ℍ ℂ))

local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ ℍ)

local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ ℍ))

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]

open scoped schurMul

open scoped FiniteDimensional

variable {A : Type*} [ha : starAlgebra A] [hA : QuantumSet A]

open scoped ComplexOrder

theorem Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam
  [hA2 : QuantumSetDeltaForm A] {x : l(A)} (hx : LinearMap.IsReal x) :
    QamReflexive (Qam.reflexiveComplement x) ↔ QamReflexive x := by
  rw [Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
    Qam.complement'_is_reflexive_iff]
  exact Qam.complement''_is_irreflexive_iff hx

end
