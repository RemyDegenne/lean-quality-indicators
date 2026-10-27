public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

attribute [local instance] Fintype.ofFinite

local notation "Γ₀Q(" N ")" => Subgroup.map (mapGL ℚ) (Gamma0 N)

local notation "Coset₀(" N ")" => HeckeCoset (Delta0 N) (Γ₀Q(N)) (Γ₀Q(N))

/-- The integral `Γ₀(N)` Hecke ring acts on modular forms of weight `k` and nebentypus `χ`. -/
noncomputable def heckeRingHomCharSpace :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →+* Module.End ℂ (modFormCharSpace k χ) where
  toFun := twistedHeckeSlashModularFormCharLinearMap k χ
  map_zero' := (twistedHeckeSlashModularFormCharLinearMap k χ).map_zero
  map_one' := twistedHeckeSlashModularFormCharLinearMap_one k χ
  map_add' := (twistedHeckeSlashModularFormCharLinearMap k χ).map_add
  map_mul' := twistedHeckeSlashModularFormCharLinearMap_map_mul k χ

end HeckeRing.GL2
end
