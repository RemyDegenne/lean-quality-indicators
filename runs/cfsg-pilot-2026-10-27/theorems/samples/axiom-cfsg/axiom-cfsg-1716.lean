public section

namespace CFSG.Sporadic.Bridge.VecSurj

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.SurjD.Native TauCeti

variable (D : VecData) (S : Spec) (G : Array Table)

variable {D S G}

variable {c : ℕ} (hF : Facts D c) (hB : BridgeFacts D S G) (gG : ℕ → J D)
  (hG : ∀ l < G.size, Rep D.n G[l]! (gG l))

include hF hB hG

omit hF hB hG

include hF hB hG

omit hF hB hG

include hF hB hG

omit hF hB hG

variable (P : GroupPresentation)

variable {P}

include hF hB hG

omit hB

theorem nonempty_mulEquiv_of_card_le (hm : P.generatorCount = S.m)
    (hrels : P.relatorLetters = S.rels)
    (hcheck : wordChecks D.n S G (O D).alpha (O D).beta = true) [Finite P.Group] {k : ℕ}
    (hcard : Nat.card P.Group ≤ k) (hk : k ≤ Nat.card (J D)) : Nonempty (J D ≃* P.Group) := by
  obtain ⟨φ, hφ⟩ := exists_surjective hF gG hG hm hrels hcheck
  exact nonempty_mulEquiv_of_surjective φ hφ hcard hk

end CFSG.Sporadic.Bridge.VecSurj
end
