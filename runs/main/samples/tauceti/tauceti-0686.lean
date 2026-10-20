public section

open Function Polynomial Set

namespace TauCeti

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : ι → X → ℝ[X]}

namespace Delineation

section

variable [PreconnectedSpace X] {n : ℕ} {θ : Fin n → X → ℝ} {m : ι → Fin n → ℕ}
  (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
  (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
  (hθ : ∀ i, Continuous (θ i)) (hmono : ∀ x, StrictMono fun i ↦ θ i x)
  (hmult : ∀ k i x, (P k x).rootMultiplicity (θ i x) = m k i)
  (hroots : ∀ k x, P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, θ i x = t)
  (hpos : ∀ i, ∃ k, 0 < m k i)

@[simp]
theorem ofRoots_root
    (i : Fin (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).count) (x : X) :
    (ofRoots hcoeff hnull hdeg hθ hmono hmult hroots hpos).root i x =
      θ (Fin.cast (ofRoots_count hcoeff hnull hdeg hθ hmono hmult hroots hpos) i) x := (rfl)

end
end Delineation
end TauCeti
end
