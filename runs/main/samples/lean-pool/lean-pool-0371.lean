@[expose] public section

namespace BGS.Markoff

noncomputable section

theorem cageFirstPointCanonical_mem
    {R : Type*} [CommRing R]
    (axis other : NormalizedCoordinateAxis) (xi middle : R)
    {x : NormalizedPoint R}
    (hOuter : x ∈ normalizedFiberAt axis xi)
    (hMiddle : normalizedCoordinateAt (cageBridgeAxis axis other) x = middle) :
    (cageFirstPointCanonicalEquiv R axis other) x ∈
      normalizedFiberAt .first xi ∧
    normalizedCoordinateAt .third
      ((cageFirstPointCanonicalEquiv R axis other) x) = middle := by
  cases axis <;> cases other <;>
    simp only [cageFirstPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv, Equiv.trans_apply, Equiv.refl_apply,
      normalizedFiberAt, normalizedCoordinateAt, cageBridgeAxis]
      at hOuter hMiddle ⊢
  all_goals
    refine ⟨⟨?_, hOuter.2⟩, ?_⟩
    · have hSurface := hOuter.1
      dsimp [IsNormalizedMarkoff, normalizedPolynomial] at hSurface
      dsimp [IsNormalizedMarkoff, normalizedPolynomial,
        normalizedSwap12, normalizedSwap23]
      ring_nf at hSurface ⊢
      exact hSurface
    · exact hMiddle

end
end BGS.Markoff
end
