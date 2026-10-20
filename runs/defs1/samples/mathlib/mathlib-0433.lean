@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

variable (I)

/--
For `I` an integral ideal of `K`, the group morphism from the torsion of `K` to `(𝓞 K ⧸ I)ˣ`.
-/
def Ideal.torsionMapQuot : (Units.torsion K) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict (torsion K)

end torsionMapQuot
end
