namespace OAI

universe uI uG uH

namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

theorem map_oddSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (oddSubsetProduct t x) = oddSubsetProduct t (fun S => f (x S)) := by
  simp only [oddSubsetProduct, map_prod]

end CirculantHadamard
end OAI
