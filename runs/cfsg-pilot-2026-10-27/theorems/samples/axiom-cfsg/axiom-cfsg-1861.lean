public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {z : V}

theorem a9_fun_exists (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0) (f : Fin 9 → ZMod 3)
    (hf : ∑ i, f i = 0) (d : ZMod 3) :
    ∃ φ : Module.Dual (ZMod 3) V, ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, f i * u i + c * d := by

  have hF : Function.Surjective (hdRo7A9BasicAux_pairMap θ z) :=
    hdRo7A9BasicAux_pairMap_surjective hfr
  have hker : LinearMap.ker (hdRo7A9BasicAux_pairMap θ z) ≤
      LinearMap.ker (hdRo7A9BasicAux_form f d) := by
    rintro ⟨⟨u, hu⟩, c⟩ hx
    have hx' : θ u + c • z = 0 := by
      simpa [hdRo7A9BasicAux_pairMap] using hx
    obtain ⟨hc0, κ, huκ⟩ := hdRo7A9BasicAux_const_of_ker hfr hM hu hx'
    have hsum0 : ∑ i, f i * u i = 0 := by
      calc ∑ i, f i * u i = ∑ i, f i * κ :=
            Finset.sum_congr rfl fun i _ => by rw [huκ]
        _ = (∑ i, f i) * κ := by rw [Finset.sum_mul]
        _ = 0 := by rw [hf, zero_mul]
    have hGval : hdRo7A9BasicAux_form f d (⟨u, hu⟩, c) =
        ∑ i, f i * u i + c * d := by
      rw [hdRo7A9BasicAux_form_apply]
    show hdRo7A9BasicAux_form f d (⟨u, hu⟩, c) = 0
    rw [hGval]
    simp [hsum0, hc0]
  refine ⟨hdRo7A9BasicAux_liftQ (hdRo7A9BasicAux_pairMap θ z) hF
    (hdRo7A9BasicAux_form f d) hker, ?_⟩
  intro u hu c
  have h := hdRo7A9BasicAux_liftQ_apply (hdRo7A9BasicAux_pairMap θ z) hF
    (hdRo7A9BasicAux_form f d) hker (⟨u, hu⟩, c)
  rw [show hdRo7A9BasicAux_pairMap θ z (⟨u, hu⟩, c) = θ u + c • z from by
    simp [hdRo7A9BasicAux_pairMap]] at h
  rw [h]
  simp [hdRo7A9BasicAux_form_apply]

end CFSG.StandardType.HdRo7A3.Small
end
