public noncomputable section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.Steinberg.Minuscule

open scoped commutatorElement

local notation "𝔽" => GaloisField 2 (2 * 1)

local notation "σ₀" => sigma (GaloisField 2 (2 * 1)) (frobQ 2 1)

local instance :
    NeZero (twistedE6Datum 2 1).rank :=
  ⟨by show (4 : ℕ) ≠ 0; decide⟩

local instance : NeZero (Tag.rank .F4) := ⟨by decide⟩

theorem rhoPerm_e6n_two : rhoPerm (e6n 2) = e6n 4 := by decide

end CFSG.EvenSmallLie.TwoE6
end
