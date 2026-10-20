@[expose] public section

open Filter Set Int

open Function hiding Commute

open scoped Topology

namespace CircleDeg1Lift

variable (f g : CircleDeg1Lift)

@[gcongr, mono] theorem mono {x y} (h : x ≤ y) : f x ≤ f y := f.monotone h

end CircleDeg1Lift
end
