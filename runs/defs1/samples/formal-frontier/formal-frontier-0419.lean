set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

/-- A presented elementary symbol. -/
def generator (p : Root ι) (a : R) : Presented ι R := PresentedGroup.of (p, a)

end Steinberg
end
