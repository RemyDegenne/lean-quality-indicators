@[expose] public section

namespace Supernatural

@[simp]
theorem ofPNat_one : ofPNat 1 = 1 := by
  ext p
  simp [ofPNat, exponent]

end Supernatural
end
