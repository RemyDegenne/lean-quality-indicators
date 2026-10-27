namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule

attribute [-instance] WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Topology Filter

open LanglandsTunnell.CubicInduction

namespace WsB

namespace T2

def realM (e : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := e.map ofRealHom

end T2
end WsB
end
end P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule
