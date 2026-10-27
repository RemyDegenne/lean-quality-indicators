namespace P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple

set_option autoImplicit false

set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

noncomputable section

namespace Ws23

namespace Cover

open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

open NumberField.AdelicVolume NumberField.AdelicCentre

variable (F : Type) [Field F] [NumberField F]

def unitF (ε : (𝓞 F)ˣ) : Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) ε

end Cover
end Ws23
end
end P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
