public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix MulOpposite MvPolynomial Representation
  TensorProduct

open Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint

open scoped MatrixGroups Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w : ℕ}

variable (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (hD : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2)

variable [Finite (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]

noncomputable local instance :
    Fintype (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The Hecke operator of a double coset on modular symbols.** For `D = Γ₁' δ Γ₂' = ⊔ᵥ Γ₁' aᵥ`
with `Γᵢ' = Γᵢ.map (mapGL ℚ)`, this is the `R`-linear map `𝕄_w(Γ₂; R) → 𝕄_w(Γ₁; R)` sending
`{α, β} ⊗ P` to `∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)` (`heckeSymbol_symbol`). It is the descent to the
`Γ₂`-coinvariants of the Hecke sum `HeckeCoset.heckeSum` of `D` on `symbolIntRep`, and it depends
on the double coset alone, not on the representatives (`heckeSymbol_symbol_eq_sum_of_rightCosets`).

The hypothesis `hD` is what lets the representatives act integrally: the chosen `D.out` is an
integral matrix, and `Γ₂` consists of them, so every representative does
(`DoubleCoset.rightCosetRep_mem`). Nothing is asked of the rest of `Δ`; for the double cosets of
the modular-forms theory the hypothesis is supplied by `Delta0_le_intEntries`. -/
noncomputable def heckeSymbol : ModularSymbols R Γ₂ w →ₗ[R] ModularSymbols R Γ₁ w :=
  Coinvariants.lift _
    (HeckeCoset.heckeSum D (symbolIntRep R w) hD (map_mapGL_le_intEntries 2 Γ₂)
      (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w))
    fun γ ↦ by
      have h := HeckeCoset.heckeSum_comp_of_mem D (symbolIntRep R w) hD
        (map_mapGL_le_intEntries 2 Γ₂) (map_mapGL_le_intEntries 2 Γ₁)
        (fun _ hγ ↦ mk_comp_symbolIntRep_of_mem Γ₁ hγ) (Subgroup.mem_map_of_mem (mapGL ℚ) γ.2)
      rwa [symbolIntRep_mapGL] at h

end TauCeti.ModularSymbols
end
