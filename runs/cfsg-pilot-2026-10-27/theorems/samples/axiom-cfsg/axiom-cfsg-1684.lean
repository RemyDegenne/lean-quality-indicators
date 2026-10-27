public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.ChainArrays CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem isConj_of_conj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsD) {y : titsD}
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsD) (h : g * y * g⁻¹ = x) :
    IsConj y ⟨x, hx⟩ :=
  isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using h)⟩

end CFSG.Sporadic.Schreier.Tits
end
