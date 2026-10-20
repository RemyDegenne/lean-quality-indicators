@[expose] public section

open CategoryTheory Convexity

namespace IsCoveringMap

section ContinuousMap

universe u v w z

variable {A : Type u} {B : Type v} {E : Type w} {X : Type z}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace X]
  {p : C(E, X)}

theorem bijective_continuousMap_lift_precomp (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] [PreconnectedSpace B]
    (f : C(A, X)) (r : C(B, A)) (b : B) :
    Function.Bijective
      (fun g : {g : C(A, E) // p.comp g = f} =>
        (⟨g.val.comp r, by rw [← ContinuousMap.comp_assoc, g.property]⟩ :
          {g : C(B, E) // p.comp g = f.comp r})) := by
  constructor
  · intro g h he
    apply (hp.continuousMapLiftEquiv f (r b)).injective
    apply Subtype.ext
    exact congrArg (fun q : {g : C(B, E) // p.comp g = f.comp r} => q.val b) he
  · intro h
    let e : {e : E // p e = f (r b)} :=
      ⟨h.val b, congrArg (fun q : C(B, X) => q b) h.property⟩
    let g := (hp.continuousMapLiftEquiv f (r b)).symm e
    refine ⟨g, Subtype.ext (ContinuousMap.coe_injective ?_)⟩
    refine hp.eq_of_comp_eq (g.val.comp r).continuous h.val.continuous ?_ b
      (hp.continuousMapLiftEquiv_symm_apply_apply f (r b) e)
    funext t
    exact (congrArg (fun q : C(A, X) => q (r t)) g.property).trans
      (congrArg (fun q : C(B, X) => q t) h.property).symm

end ContinuousMap
end IsCoveringMap
end
