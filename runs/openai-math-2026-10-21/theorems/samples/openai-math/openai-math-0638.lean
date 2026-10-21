namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38 u39 u40

section

namespace ThreeMachine.StackCompiler

theorem volume_option_le {α : Type u7} [Coding α] (o : Option α) (V : ℕ)
    (hV : ∀ a ∈ o, volume a ≤ V) : volume o ≤ V+2 := by
  cases o with
  | none => simp only [volume_none]; omega
  | some a => simpa only [volume_some,Nat.add_le_add_iff_right] using hV a rfl

end ThreeMachine.StackCompiler
end
end OAI
