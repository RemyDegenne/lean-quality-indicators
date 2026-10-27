public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Core

variable {F : Type} [Field F]

theorem k32_l3_unitri_eq {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) =
      k32U3 ((u : Matrix (Fin 3) (Fin 3) F) 0 1) ((u : Matrix (Fin 3) (Fin 3) F) 0 2)
        ((u : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hu
  exact k32U3_eq_of_entries (hlow 1 0 (by decide)) (hlow 2 0 (by decide)) (hlow 2 1 (by decide))
    (hdiag 0) (hdiag 1) (hdiag 2)

end Core
end CFSG.QuasithinUnique.DoubleA3
end
