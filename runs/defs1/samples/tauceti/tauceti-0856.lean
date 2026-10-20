public section

namespace TauCeti

universe u v

variable {p : ℕ} [hp : Fact p.Prime]

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace IsProP

variable {H : Type v} [Group H] [TopologicalSpace H]

/-- **A Frattini cover with a continuous homomorphic section is an isomorphism.** A continuous
homomorphism `φ : G → H` out of a pro-`p` group `G`, whose kernel lies in the Frattini subgroup
`Φ(G)` and which has a continuous homomorphic section `s`, is a topological isomorphism whose
inverse is `s`. -/
noncomputable def continuousMulEquivOfLeftInverse (hG : IsProP p G) (φ : G →ₜ* H) (s : H →ₜ* G)
    (hs : Function.LeftInverse φ s) (hker : φ.toMonoidHom.ker ≤ proPFrattini p G) : G ≃ₜ* H where
  toFun := φ
  invFun := s
  left_inv x := by
    obtain ⟨y, rfl⟩ := hG.surjective_of_leftInverse_of_ker_le_proPFrattini hs hker x
    exact congrArg s (hs y)
  right_inv := hs
  map_mul' := map_mul φ
  continuous_toFun := φ.continuous
  continuous_invFun := s.continuous

end IsProP
end TauCeti
end
