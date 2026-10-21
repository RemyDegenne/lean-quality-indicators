namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n

local notation "sides" => allocatedPrincipalSides B U basis S

local notation "short" => allocatedShortAxis (I := I) U basis S.value

local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

local notation "Input" => PrincipalTupleIndex B degree

local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]

variable {q : ℕ}

variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)

variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)

variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))

variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

include hlen hfixed hactive in
theorem allocatedFiberActiveContainedProgression_eq_common
    (v : ∀ j : ActiveInput,
      IntegerScalarCubeBox Empty (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))) :
    allocatedActiveContainedProgression B U basis S
      (fun j : ActiveInput => ResidueBoxSlice.fiberParameterStride
        (keep := keep) (q := q) (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed) v =
    allocatedActiveContainedProgression B U basis S (fun _ => q)
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_common_contained B U basis S slice hlen fixed hfixed hactive) v := by
  funext j a
  apply Subtype.ext
  simp only [allocatedActiveContainedProgression, ResidueBoxSlice.fiberParameterStride,
    ite_eq_left (hactive j)]

end Erdos3.VectorPolynomial
end
end OAI
