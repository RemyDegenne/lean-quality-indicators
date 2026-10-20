public section

namespace TauCeti

universe u v

namespace ClassFunction

variable {k : Type u} {G : Type v} [Group G] [Fintype G]

variable [Field k]

@[simp]
theorem characterPairing_ofFDRep_self [Invertible (Nat.card G : k)] [IsAlgClosed k]
    (V : FDRep k G) [CategoryTheory.Simple V] :
    characterPairing (ofFDRep V) (ofFDRep V) = 1 := by
  classical
  have hrefl : Nonempty (V ≅ V) := ⟨CategoryTheory.Iso.refl V⟩
  rw [characterPairing_ofFDRep_orthonormal V V, ite_eq_left hrefl]

end ClassFunction
end TauCeti
end
