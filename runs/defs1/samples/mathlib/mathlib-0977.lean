@[expose] public section

variable {M : Type*} [Monoid M]

open Units

open scoped Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`. -/
@[to_additive /-- The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. -/]
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

end
