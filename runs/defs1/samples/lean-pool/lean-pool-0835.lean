@[expose] public section

variable {C : FloatCfg}

/-- Normalize a representation whose mantissa has reached the precision by
incrementing the exponent and zeroing the mantissa. -/
def FloatRep.normalize (f : FloatRep C) : FloatRep C :=
  if f.m = C.prec then
    ⟨f.s, f.e + 1, 0⟩
  else
    f

end
