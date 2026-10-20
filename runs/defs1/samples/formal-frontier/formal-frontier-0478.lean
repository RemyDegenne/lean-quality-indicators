@[expose] public section

namespace Supernatural

/-- Embedding positive naturals into supernatural numbers. -/
def ofPNatHom : ℕ+ →* Supernatural where
  toFun := ofPNat
  map_one' := ofPNat_one
  map_mul' := ofPNat_mul

end Supernatural
end
