@[expose] public section

namespace Stafford38.Characteristic.CanonicalGradedTangentialEquivalences

open Stafford38.Characteristic

open Stafford38.Characteristic.CanonicalFilteredTwoTerm

open Stafford38.Characteristic.CanonicalTotalGradedBridge

open Stafford38.Characteristic.CanonicalTotalGradedActionCompatibility

open Stafford38.Characteristic.CanonicalTangentialTotalAction

open Stafford38.Characteristic.CanonicalOldTangentialFiniteness

open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness

open Stafford38.Characteristic.CanonicalTangentialRingEquivalence

open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness

open Stafford38.Characteristic.NormalSymbolPolynomial

open Stafford38.CharacteristicAssociatedGradedModule

open Stafford38.WeylIteratedEquivalence

open Stafford38.WeylPBWMonicBridge

open Stafford38.WeylQuotientTransport

noncomputable section

variable (k : Type*) [Field k]

variable (n N : ℕ) (d : PresentedWeyl k (n + 1))

variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

/-- The order-associated graded module of the canonical right-ideal quotient. -/
abbrev Graded := OrderAssociatedGradedModule k (presentedCanonicalRightIdeal (k := k) n N d)

end
end Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
end
