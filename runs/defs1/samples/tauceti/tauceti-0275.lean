public section

open CategoryTheory Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (hPhi : Phi.IsRegular)

/-- The canonical inclusion of the coordinate-free complex torus into the realization of a
nonempty regular fan, obtained by translating the distinguished point of the zero cone.
By proof irrelevance, different nonemptiness witnesses give definitionally equal inclusions. -/
noncomputable def analyticTorusι (hPhi0 : Nonempty Phi.cones) (t : ComplexTorus N) :
    Phi.analyticRealization hPhi :=
  t • Phi.analyticDistinguishedPoint hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩

end TauCeti.Toric.Fan
end
