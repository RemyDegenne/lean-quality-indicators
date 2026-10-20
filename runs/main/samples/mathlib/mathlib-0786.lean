@[expose] public section

namespace PNat

@[gcongr, mono]
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.monotone

end PNat
end
