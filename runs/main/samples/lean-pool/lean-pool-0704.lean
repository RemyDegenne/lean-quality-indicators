@[expose] public section

namespace BGS.Markoff

universe u

theorem normalizedZeroFiber_meets_distinctAxis
    {R : Type u} [CommRing R]
    (i : R) (hi : i ^ 2 = -1)
    {axis other : NormalizedCoordinateAxis} (haxis : axis ≠ other) (b : R) :
    NormalizedFibersMeet (normalizedFiberAt axis 0) (normalizedFiberAt other b) := by
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · exact (haxis rfl).elim
  · exact normalizedFiber1_zero_meets_fiber2 i b hi
  · exact normalizedFiber1_zero_meets_fiber3 i b hi
  · rcases normalizedFiber1_zero_meets_fiber2 i b hi with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim
  · rcases normalizedFiber1_zero_meets_fiber3 i b hi with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · rcases normalizedFiber1_zero_meets_fiber3 i b hi with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · rcases normalizedFiber1_zero_meets_fiber2 i b hi with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim

end BGS.Markoff
end
