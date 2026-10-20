@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

variable (I)

variable {I} [NumberField K]

theorem Ideal.torsionMapQuot_inj (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) {x y : torsion K} :
    torsionMapQuot I x = torsionMapQuot I y ↔ x = y :=
  (torsionMapQuot_injective hI₁ hI₂).eq_iff

end torsionMapQuot
end
