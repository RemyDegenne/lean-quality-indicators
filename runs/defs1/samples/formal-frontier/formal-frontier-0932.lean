set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

/-- An off-diagonal position and a ring coefficient. -/
abbrev Generator (ι : Type uι) (R : Type uR) := Root ι × R

end Steinberg
end
