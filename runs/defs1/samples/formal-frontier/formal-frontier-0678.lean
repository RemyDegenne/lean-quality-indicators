@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

variable {G}

variable {P : ProfiniteGrp.{u}} [IsProP p P]

/-- Every continuous homomorphism from a profinite group to a pro-`p`
group factors through its maximal pro-`p` quotient. -/
noncomputable def lift (f : G →ₜ* P) : product p G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram p G)).π.app (preimage p f H) ≫
      (ofFiniteGrpHom <| quotientMap p f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      change quotientMap p f Y (x <| preimage p f Y) =
        P.diagram.map g (quotientMap p f X (x <| preimage p f X))
      have hxy := hx (preimage_le (p := p) (f := f) g.le).hom
      obtain ⟨t, ht⟩ : ∃ t : G,
          QuotientGroup.mk t = x (preimage p f X) :=
        QuotientGroup.mk_surjective (x (preimage p f X))
      rw [← hxy, ← ht]
      have hp := P.cone.π.naturality g
      apply_fun fun q ↦ q (f t) at hp
      exact hp
  }⟩

end MaximalProPQuotient
end ProfiniteGrp
end
