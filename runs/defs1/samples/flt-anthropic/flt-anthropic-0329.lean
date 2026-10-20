namespace P2MW.S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal

set_option autoImplicit false

set_option linter.unusedSectionVars false

open IsLocalRing

open scoped TensorProduct Pointwise

open scoped AdicCompletion.GaloisAction

namespace AdicCompletion

namespace ComplFiniteAux

p2m_open

p2m_open

section Setting

variable (B : Type) {C : Type} [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C]
  [Module.Finite B C] (𝔫 : Ideal C) [𝔫.IsMaximal]

local notation "J" => Ideal.comap (algebraMap B C) 𝔫

local notation "B̂" => AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B

local notation "Ĉ" => AdicCompletion 𝔫 C

omit [IsNoetherianRing B] [Module.Finite B C] in

abbrev idx : {P : Ideal C // P.IsMaximal ∧ (J).map (algebraMap B C) ≤ P} :=
  ⟨𝔫, ‹𝔫.IsMaximal›, map_J_le B 𝔫⟩

end Setting
end ComplFiniteAux
end AdicCompletion
end P2MW.S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
