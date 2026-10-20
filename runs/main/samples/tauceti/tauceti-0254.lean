public section

open QuadraticMap

namespace TauCeti.QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

theorem det_list_prod_of_reflectionOrthogonal [FiniteDimensional K V]
    (Q : QuadraticForm K V) (l : List (QuadraticMap.orthogonalGroup Q))
    (hl : ∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)),
      QuadraticMap.reflectionOrthogonal Q v = r) :
    LinearEquiv.det (l.prod : V ≃ₗ[K] V) = (-1 : Kˣ) ^ l.length := by
  rw [← _root_.QuadraticMap.orthogonalDet_apply, map_list_prod,
    ← List.length_map (_root_.QuadraticMap.orthogonalDet Q)]
  apply List.prod_eq_pow_length
  rw [List.forall_mem_map]
  intro r hr
  obtain ⟨v, _, rfl⟩ := hl r hr
  rw [_root_.QuadraticMap.orthogonalDet_apply,
    TauCeti.QuadraticMap.coe_reflectionOrthogonal, TauCeti.QuadraticMap.det_reflection]

end TauCeti.QuadraticMap
end
