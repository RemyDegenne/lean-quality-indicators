@[expose] public section

namespace ErdosProblems.MulticolourTriangleRamsey

open Filter Finset SimpleGraph

open scoped Topology

theorem recursiveCrossColour_same_right_coordinate
    {K : Type*} [DecidableEq K] {H s : ℕ}
    (P Q : Finset K) (a b : Fin s ↪ K)
    (ha : ∀ d, a d ∈ Q \ P)
    (_hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y y' : Fin s → Fin H) (colour : K)
    (hactive : colour ∉ Q)
    (hxy : recursiveCrossColour a b f g hcover x y = colour)
    (hxy' : recursiveCrossColour a b f g hcover x y' = colour) :
    ∃ d : Fin s, colour = b d ∧ y d = y' d := by
  have select (z : Fin s → Fin H)
      (hz : recursiveCrossColour a b f g hcover x z = colour) :
      ∃ d : Fin s, colour = b d ∧ z d = g x d := by
    have hbackward :=
      (recursiveCrossColour_spec a b f g hcover x z).resolve_left (by
        rintro ⟨d, hd, _⟩
        apply hactive
        rw [← hz, hd]
        exact (Finset.mem_sdiff.mp (ha d)).1)
    obtain ⟨d, hd, hforced⟩ := hbackward
    exact ⟨d, hz.symm.trans hd, hforced⟩
  obtain ⟨d, hd, hforced⟩ := select y hxy
  obtain ⟨d', hd', hforced'⟩ := select y' hxy'
  have hindex : d = d' := b.injective (hd.symm.trans hd')
  exact ⟨d, hd, hforced.trans (by simpa [hindex] using hforced'.symm)⟩

end ErdosProblems.MulticolourTriangleRamsey
end
