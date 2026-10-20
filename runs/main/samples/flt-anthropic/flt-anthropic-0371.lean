namespace P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

set_option Elab.async false

open scoped TensorProduct

open MvPowerSeries

universe u v

namespace MvFormalGroup

namespace PowerDefect

p2m_open

section Realise

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]

variable (E : Type u) [CommRing E] [Bialgebra 𝓞 E] [Coalgebra.IsCocomm 𝓞 E] (c₂ : Fin d → E ⊗[𝓞] E)
  (hc₂ : ∀ j, c₂ j ∈ Ideal.span {(p : E ⊗[𝓞] E)})

variable (g : Type u) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]

omit [Φ.IsComm] [Coalgebra.IsCocomm 𝓞 E] [IsAdicComplete (Ideal.span {(p : g)}) g] in
theorem cpt_val_mem (f h : WithConv (E →ₐ[𝓞] g)) (j : Fin d) :
    (cpt p Φ E c₂ hc₂ g f h).val j ∈ Ideal.span {(p : g)} :=
  map_mem_span_natCast _ p (hc₂ j)

end Realise
end PowerDefect
end MvFormalGroup
end P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle
