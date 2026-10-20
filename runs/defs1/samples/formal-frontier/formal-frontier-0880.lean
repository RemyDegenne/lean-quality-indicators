@[expose] public section

namespace Supernatural

/-- Embed all natural numbers into supernatural numbers, sending zero to top. -/
def ofNat : ℕ → Supernatural
  | 0 => ⊤
  | n + 1 => ofPNat ⟨n + 1, Nat.succ_pos n⟩

end Supernatural
end
