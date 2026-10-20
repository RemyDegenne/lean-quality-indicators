@[expose] public section

universe uR uA uM

namespace LinearMap

theorem splitKernelProjection_prod_eq_kerProdEquivOfRightInverse_symm
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] A) (g : A →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) :
    (splitKernelProjection g f hfg).prod f =
      (kerProdEquivOfRightInverse f g hfg).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · apply Subtype.ext
    exact (splitKernelProjection_apply g f hfg x).trans
      (kerProdEquivOfRightInverse_symm_fst f g hfg x).symm
  · exact (kerProdEquivOfRightInverse_symm_snd f g hfg x).symm

end LinearMap
end
