@[expose] public section

open Function Set

universe u v

namespace Cardinal

attribute [local simp] toENatAux_nat toENatAux_zero toENatAux_ofENat

@[simp] lemma toENat_ofNat (n : ℕ) [n.AtLeastTwo] : toENat ofNat(n) = ofNat(n) := toENat_nat _

end Cardinal
end
