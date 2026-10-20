public section

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

theorem eq_weylSign_of_forall_ofIdx {f : P.weylGroup →* ℤˣ}
    (hf : ∀ i : ι, f (RootPairing.weylGroup.ofIdx P i) = -1) : f = weylSign P b := by
  -- `ext` would descend past `MonoidHom.ext` into `Units.ext`, leaving the goal about the
  -- underlying integers; the homomorphism extensionality is the one the induction needs.
  refine MonoidHom.ext fun w ↦ ?_
  have hw : w ∈ Subgroup.closure (range fun i : b.support =>
      RootPairing.weylGroup.ofIdx P (i : ι)) := by
    rw [← weylGroup_eq_closure_simple P b]
    exact Subgroup.mem_top w
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hf, weylSign_ofIdx]
  | one => rw [map_one, map_one]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, map_inv, hx]

end TauCeti
end
