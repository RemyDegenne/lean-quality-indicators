@[expose] public section

universe uR uM uN uP uι uκ

namespace Module.IsStablyFree

variable {R : Type uR} [Ring R]

variable {M : Type uM} [AddCommGroup M] [Module R M]

variable {N : Type uN} [AddCommGroup N] [Module R N]

theorem ker_of_surjective [IsStablyFree R M] [Module.Finite R N]
    [IsStablyFree R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    IsStablyFree R (LinearMap.ker f) := by
  classical
  let K := LinearMap.ker f
  obtain ⟨T, hTgroup, hTmodule, hTfinite, hTfree, hMfree⟩ :=
    IsStablyFree.exist_free_prod R M
  let _ : AddCommGroup T := hTgroup
  let _ : Module R T := hTmodule
  let _ : Module.Finite R T := hTfinite
  let _ : Module.Free R T := hTfree
  let _ : Module.Free R (M × T) := hMfree
  obtain ⟨Q, hQgroup, hQmodule, hQfinite, hQfree, hNQfree⟩ :=
    IsStablyFree.exist_free_prod R N
  let _ : AddCommGroup Q := hQgroup
  let _ : Module R Q := hQmodule
  let _ : Module.Finite R Q := hQfinite
  let _ : Module.Free R Q := hQfree
  let _ : Module.Free R (N × Q) := hNQfree
  let split : (N × K) ≃ₗ[R] M := Module.Projective.prodKerEquivOfSurjective f hf
  let e : (K × ((N × Q) × T)) ≃ₗ[R] ((M × T) × Q) :=
    (LinearEquiv.prodAssoc R K (N × Q) T).symm |>.trans
      (((LinearEquiv.prodAssoc R K N Q).symm).prodCongr (LinearEquiv.refl R T)) |>.trans
      (((LinearEquiv.prodComm R K N).prodCongr (LinearEquiv.refl R Q)).prodCongr
        (LinearEquiv.refl R T)) |>.trans
      (LinearEquiv.prodAssoc R (N × K) Q T) |>.trans
      ((LinearEquiv.refl R (N × K)).prodCongr (LinearEquiv.prodComm R Q T)) |>.trans
      (LinearEquiv.prodAssoc R (N × K) T Q).symm |>.trans
      ((split.prodCongr (LinearEquiv.refl R T)).prodCongr (LinearEquiv.refl R Q))
  let _ : Module.Free R (K × ((N × Q) × T)) := Module.Free.of_equiv e.symm
  exact IsStablyFree.of_free_prod R K ((N × Q) × T)

end Module.IsStablyFree
end
