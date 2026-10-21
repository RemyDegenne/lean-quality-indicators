# Test-retest: `gpt-6.1-sol-high-repeat-2` vs `gpt-6.1-sol-high`, run `main`

The second pass judged each theorem in a fresh session, without the first verdict.

| Library | Flags re-flagged | Non-flags flagged | Same hypothesis | κ |
|---|---:|---:|---:|---:|
| Mathlib | 12/12 (76%–100%) | 0/288 (0%–1%) | 12/12 | 1.00 |
| Tau Ceti | 18/18 (82%–100%) | 1/282 (0%–2%) | 18/18 | 0.97 |
| Lean Pool | 60/61 (91%–100%) | 0/239 (0%–2%) | 58/60 | 0.99 |
| FLT (Anthropic) | 78/79 (93%–100%) | 0/221 (0%–2%) | 78/78 | 0.99 |
| Formal Frontier | 17/17 (82%–100%) | 1/283 (0%–2%) | 17/17 | 0.97 |

Overall κ: 0.99 (on the 1500 theorems judged by both passes).

## Mathlib: 0 disagreements

## Tau Ceti: 1 disagreements

### [`TauCeti.DynkinType.geckGroupScheme_hom_ext`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/GroupScheme.lean#L331-L352) — `tauceti-0084`: flagged only second

- `(htorus : t.geckWeightTorus ht ≫ φ = t.geckWeightTorus ht ≫ ψ)`: Agreement on root subgroups already implies agreement on the torus. The source lemma kostantCoordinateCocharacter_torusCharacter_mem_kostantElementarySubgroup, applied to a torus point supported at i with value u, puts the i-th coordinate-cocharacter at u² in the elementary subgroup: rootGeneratorWeight_inl and cartanMatrix_apply_same give exponent 2, and isSl2Triple_geckRepresentation supplies the triple. Taking products, every represented coordinatewise-square torus point is elementary. Thus hroot gives agreement after precomposing the torus restrictions with the squaring morphism. Its coordinate map on ℤ[Fin t.rank →₀ ℤ] sends each monomial indexed by m to that indexed by 2m and is injective, since doubling integer exponent vectors is injective. Cancel this map on coordinate morphisms to obtain htorus, then use the original proof. This does not assume units have square roots or Cartan rows are primitive; the argument also covers rank one, characteristic-two points, and an empty index set.

## Lean Pool: 1 disagreements

### [`NavierStokes.ActualCycleCoherence.source_fiber_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActualCycleCoherence.lean#L714-L723) — `lean-pool-0279`: flagged first, not again

- `(hS : ∀ l n, IsClosed (S l n))`: Split on 0 < p.1. In the positive case, compose source_positive_smooth H with the fiber inclusion; this lemma requires neither hS nor hpos. Otherwise the fiber source is identically zero: H.inputSupport and hpos make every nonzero real-projected input coefficient vanish throughout the domain where the radius is nonpositive. This property is preserved by the literal residual operations. In particular, a function vanishing on that half-space has zero total Fréchet derivative there, including at radius zero: any existing derivative vanishes by one-sided directional limits; a nonexistent derivative totalizes to zero (fderiv_zero_of_not_differentiableAt). HarmonicFields.derivativeCoefficient therefore preserves this vanishing, as do convolution, angular differentiation and real projection. The residual's zero mode is zero by ParticularWaveAssembly.residualSource_zero. Thus the nonpositive-radius fiber is constant zero, without any closedness assumption on S.

## FLT (Anthropic): 1 disagreements

### [`P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.lean#L856-L872) — `flt-anthropic-0062`: flagged first, not again

- `(hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)`: It follows from hτ₁. Write F = modularFunctionFieldC K p, j = jF K p and j' = jpF K p, using LevelHeckeDiff's definitions. Since A0 = K(j), hτ₁ identifies τ on A0 with phi0; this follows by IntermediateField.adjoin_algHom_ext. Applying τ to the minimal-polynomial relation for j' therefore shows PF.IsRoot (τ j'). The definition of QF and PF_isRoot_jF give PF = (X - C j) * QF. But minpoly_yR and isIntegral_yR show QF is irreducible, while QF_map and natDegree_Qexp give its degree p > 1. Thus Irreducible.not_isRoot_of_natDegree_ne_one excludes a root in F, forcing τ j' = j. Supply this derived equality to the existing proof. There are no exceptional zero cases: primality gives p ≥ 2, and hζ gives (p : K) ≠ 0. The two swapping hypotheses can each be deleted separately, but not both.
- `(hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)`: Retaining hτ₂ gives τ.symm j = j'. Apply the implication proved in the preceding justification to τ.symm: any such automorphism sending j to j' must send j' to j. Hence τ.symm j' = j, equivalently τ j = j', recovering hτ₁ for the existing proof. The same prime and primitive-root assumptions exclude the degenerate cases. This deletion retains hτ₂; the two swapping hypotheses cannot both be removed.

## Formal Frontier: 1 disagreements

### [`Module.Basis.exists_basis_subset_finset_of_le_jacobson`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/LinearAlgebra/Basis/Semilocal.lean#L383-L393) — `formal-frontier-0252`: flagged only second

- `(hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤ (Ideal.jacobson (⊥ : Ideal B)))`: Replace the auxiliary unit-selection argument by finite avoidance over R. Using IsLocalRing.residue_surjective, choose representatives t(a) of the infinite residue field. For distinct a,b, t(a)-t(b) is a unit by IsLocalRing.residue_ne_zero_iff_isUnit. Consequently, finitely many nonzero R-linear maps on W are simultaneously nonzero: inductively, take y avoiding the previous kernels and x outside the next kernel, then choose y+t(a)•x. Each map excludes at most one parameter unless it vanishes on x, in which case a previously avoided map excludes none. Two excluded parameters would contradict IsUnit.smul_eq_zero. Apply this to the restrictions of P.asIdeal.mkQ.comp f for all maximal ideals P. As in the existing proof, hW and surjectivity of f ensure each restriction is nonzero. The selected f-value avoids every maximal ideal, hence is a unit by exists_max_ideal_of_mem_nonunits. The existing basis-update induction then applies without hJ. Empty families cause no problem: if B is the zero ring, every value is a unit; if s is empty, retain b.

