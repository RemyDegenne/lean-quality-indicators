namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace K3Sol

p2m_open

variable {X : Scheme.{u}} {U V : X.Opens}

variable (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)

variable (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι)

variable (hlt : ∀ b a, eV b < eU a)

include hlt

section Maps

variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) (N : X.Modules)

variable (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)

local notation "FX" => OModulePresheaf.ofModules π N

local notation "FV" => OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)

local notation "AV" => Scheme.OrderedAffineCover.imageFamily 𝔙 V.ι

local notation "BU" => Scheme.OrderedAffineCover.imageFamily 𝔘 U.ι

local notation "DD" => OModulePresheaf.biCech (OModulePresheaf.ofModules π N)
  (Scheme.OrderedAffineCover.imageFamily 𝔙 V.ι) (Scheme.OrderedAffineCover.imageFamily 𝔘 U.ι)

omit hlt in

theorem d_pureU_eq_zero {m : ℕ} (y : (FX).cochain 𝔛' m) (hyU : ∀ t, y (pureU 𝔘 𝔛' eU t) = 0)
    (t : 𝔘.Idx (m + 1)) : (FX).d 𝔛' m y (pureU 𝔘 𝔛' eU t) = 0 := by
  rw [OModulePresheaf.d_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : y (𝔛'.face (pureU 𝔘 𝔛' eU t) j) = 0 := hyU (𝔘.face t j)
  rw [h0, map_zero, smul_zero]

end Maps
end K3Sol
end P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
