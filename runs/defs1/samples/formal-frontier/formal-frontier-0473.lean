@[expose] public section

universe uR uA uM

namespace LinearMap

/-- Projection from a split module onto the kernel of its retraction. -/
def splitKernelProjection
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) : M →ₗ[R] LinearMap.ker r :=
  LinearMap.codRestrict (LinearMap.ker r)
    (LinearMap.id - i.comp r) fun x ↦ by
      rw [LinearMap.mem_ker]
      change r (x - i (r x)) = 0
      apply LinearMap.injective_of_comp_eq_id i r h
      rw [map_zero]
      change (i.comp r) (x - i (r x)) = 0
      rw [map_sub, show (i.comp r) (i (r x)) = (i.comp r) x by
        change i (r (i (r x))) = i (r x)
        rw [show r (i (r x)) = r x by
          rw [← LinearMap.comp_apply, h, LinearMap.id_apply]], sub_self]

end LinearMap
end
