public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

namespace QuiverSubrep

variable {M : QuiverRep k Q}

/-- The representation carried by a subrepresentation: the submodule at each vertex, with a path
acting by the restriction of its action on `M`. -/
-- The object part is the interface here: the point of a subrepresentation is that it *is* the
-- submodule at each vertex, and statements such as `ι_app_apply` below do not even typecheck
-- unless a term of `N.toSubmodule a` is a term of `N.toQuiverRep.obj a`. Hence `@[expose]`.
@[expose]
def toQuiverRep (N : QuiverSubrep M) : QuiverRep k Q where
  obj a := ModuleCat.of k (N.toSubmodule a)
  map {_ _} p := ModuleCat.ofHom ((M.map p).hom.restrict fun _ hx ↦ N.map_mem p hx)
  map_id a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    -- `LinearMap.restrict` has no `apply` lemma for the value of the underlying map, so read the
    -- restriction of `M.map (𝟙 a)` off as that map applied to `x` before rewriting.
    change (M.map (𝟙 a)) (x : M.obj a) = (x : M.obj a)
    rw [M.map_id]
    rfl
  map_comp p q := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    -- As in `map_id`, restate the restricted maps as maps on `M`, so that `M.map_comp` applies.
    change (M.map (p ≫ q)) (x : M.obj _) = (M.map q) ((M.map p) (x : M.obj _))
    rw [M.map_comp]
    rfl

end QuiverSubrep
end TauCeti
end
