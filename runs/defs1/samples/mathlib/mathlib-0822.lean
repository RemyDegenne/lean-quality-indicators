@[expose] public section

namespace OreLocalization

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
@[instance_reducible]
def oreSetOfNoZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R}
    (oreNum : R → S → R) (oreDenom : R → S → S)
    (ore_eq : ∀ (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S :=
  letI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  oreSetOfIsCancelMulZero oreNum oreDenom ore_eq

end OreLocalization
end
