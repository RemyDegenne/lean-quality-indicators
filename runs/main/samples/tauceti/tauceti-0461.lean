public section

universe u

namespace TauCeti

theorem IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq (K M : Type*) [Field K]
    [Field M] [Algebra K M] [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) (K' : Type*) [Field K'] [Algebra K K']
    {s : Set M} (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, ∃ y : K',
      y ^ p ^ n = algebraMap K K' (IsPurelyInseparable.iterateFrobenius K M p hn x)) :
    Nonempty (M →ₐ[K] K') := by
  classical
  -- B2.0: `K'` inherits the exponential characteristic from `K`
  have : ExpChar K' p := expChar_of_injective_algebraMap (algebraMap K K').injective p
  set φ := IsPurelyInseparable.iterateFrobenius K M p hn with hφ
  set ψ := iterateFrobenius K' p n
  set θ : M →+* K' := (algebraMap K K').comp φ with hθ
  have hψ_apply : ∀ y : K', ψ y = y ^ p ^ n := fun y ↦
    iterateFrobenius_def (R := K') (p := p) (n := n) (x := y)
  -- The single computation both the `K`-algebra law (B2.2) and the `K`-linearity of the
  -- assembled embedding (B2.6) rest on: on the image of `K`, `θ` and `ψ` agree.
  have hKθ : ∀ a : K, θ (algebraMap K M a) = ψ (algebraMap K K' a) := fun a ↦ by
    rw [hθ, RingHom.comp_apply, hφ, IsPurelyInseparable.iterateFrobenius_algebraMap, hψ_apply,
      map_pow]
  -- B2.2: the good set contains the image of `K`
  have hKmem : ∀ a : K, algebraMap K M a ∈ Subfield.comap θ ψ.fieldRange := fun a ↦
    RingHom.mem_fieldRange.mpr ⟨algebraMap K K' a, (hKθ a).symm⟩
  -- B2.1 + B2.4: promote the good set and show it is everything
  set G : IntermediateField K M :=
    (Subfield.comap θ ψ.fieldRange).toIntermediateField hKmem
  have hsG : s ⊆ (G : Set M) := by
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    exact RingHom.mem_fieldRange.mpr ⟨y, by simpa [hθ, hφ, hψ_apply] using hy⟩
  have hGtop : G = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact IntermediateField.adjoin_le_iff.mpr hsG
  have hgood : ∀ x : M, θ x ∈ ψ.fieldRange := by
    intro x
    have hx : x ∈ G := by rw [hGtop]; exact IntermediateField.mem_top
    exact hx
  -- B2.6: invert `ψ` on its range. The range equivalence is taken at the RING level: `ψ` is only
  -- `K`-semilinear (along Frobenius), so no `K`-algebra equivalence is available here.
  -- name the ring map first: stating its defining property separately keeps the `AlgHom`
  -- structure's coercion out of the `commutes'` goal
  let σ : M →+* K' :=
    (ψ.rangeRestrictFieldEquiv.symm.toRingHom).comp (θ.codRestrict ψ.fieldRange hgood)
  have hσ : ∀ x : M, ψ (σ x) = θ x := fun x ↦
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ψ _
  -- `K`-linearity is forced by injectivity of `ψ`, not proved separately
  exact ⟨{ toRingHom := σ
           commutes' := fun a ↦ ψ.injective ((hσ _).trans (hKθ a)) }⟩

end TauCeti
end
