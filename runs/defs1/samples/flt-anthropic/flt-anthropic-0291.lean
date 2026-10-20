namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace GlueFromBasisSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}

variable (D : GData π B)

p2m_reactivate

namespace GData

section ClauseB

variable {F : OModulePresheaf π}

variable (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] D.M W)
  (hϑs : ∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x)
  (hϑn : ∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = D.res h (ϑ W x))

def inApp (U : V.Opens) : F.obj U →ₗ[R] D.G.obj U where
  toFun y := ⟨fun W => ϑ W.1 (F.res W.2 y), fun W W' h => by
    rw [← hϑn W.1 W'.1 h, F.res_res]⟩
  map_add' y y' := D.G_ext fun W => by
    show ϑ W.1 (F.res W.2 (y + y')) = ϑ W.1 (F.res W.2 y) + ϑ W.1 (F.res W.2 y')
    rw [map_add, map_add]
  map_smul' r y := D.G_ext fun W => by
    show ϑ W.1 (F.res W.2 (r • y)) = r • ϑ W.1 (F.res W.2 y)
    rw [LinearMap.map_smul, LinearMap.map_smul]

end ClauseB
end GData
end GlueFromBasisSol
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
