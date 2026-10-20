@[expose] public section

set_option warningAsError true

open Polynomial

open scoped TensorProduct

universe u v

noncomputable section

theorem IsLocallyNormalRing.of_etale_of_isDomain
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S] :
    IsLocallyNormalRing S := by
  let K := FractionRing R
  let P := S ⊗[R] K
  -- Keep the left S-action separate from the right K-action of the generic fibre.
  let leftAlgebra : Algebra S P := inferInstance
  let rightAlgebra : Algebra K P := Algebra.TensorProduct.rightAlgebra
  have hclosed : @IsIntegrallyClosedIn S P _ _ leftAlgebra :=
    smooth_isIntegrallyClosedIn_baseChange_fraction
  let _ : Algebra K P := rightAlgebra
  let ecomm : (K ⊗[R] S) ≃ₐ[K] P :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R K S).toRingEquiv) <| by
      intro k
      change (Algebra.TensorProduct.comm R K S) (k ⊗ₜ[R] (1 : S)) =
        (1 : S) ⊗ₜ[R] k
      rfl
  let _ : Algebra.Etale K P := Algebra.Etale.of_equiv ecomm
  have hEtale : Algebra.Etale K P := inferInstance
  obtain ⟨I, hI, L, hLfield, hLalg, e, _⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := P)).mp hEtale
  let _ : Finite I := hI
  let _ (i : I) : Field (L i) := hLfield i
  let _ (i : I) : Algebra K (L i) := hLalg i
  -- Each coordinate receives its S-action from S → P → Π i, L i.
  let _ (i : I) : Algebra S (L i) :=
    ((Pi.evalRingHom L i).comp
      (e.toRingEquiv.toRingHom.comp (@algebraMap S P _ _ leftAlgebra))).toAlgebra
  let _ : Algebra S P := leftAlgebra
  let E : P ≃ₐ[S] (∀ i, L i) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) <| by
      intro s
      ext i
      rfl
  -- Closedness already means integral closure over S itself: no integrality of S/R.
  let _ : IsIntegralClosure S S (∀ i, L i) := E.isIntegrallyClosedIn.mp hclosed
  exact integralClosure_pi_fields_isLocallyNormal (R := S) (A := S) (I := I) L

end
end
