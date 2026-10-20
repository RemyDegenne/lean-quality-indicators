# duplicates-mathlib: run `main`, judge `claude-opus-5-5-high`

| Library | Sampled | Judged | Flagged | `duplicate` | `special_case` | `proof_uses_it` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Tau Ceti | 1000 | 1000 | 50 | 0 | 50 | 34 | 5.0% | 3.8%–6.5% | $49.56 |
| Lean Pool | 1000 | 1000 | 68 | 8 | 60 | 28 | 6.8% | 5.4%–8.5% | $40.48 |
| FLT (Anthropic) | 1000 | 1000 | 137 | 12 | 125 | 51 | 13.7% | 11.7%–16.0% | $70.21 |
| Formal Frontier | 1000 | 1000 | 46 | 5 | 41 | 29 | 4.6% | 3.5%–6.1% | $56.04 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Tau Ceti (50 flagged)

### [`TauCeti.SheafOfModules.freePUnitIsoUnit_inv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/ModuleCat/Sheaf/Free/Basic.lean#L78-L84) — `tauceti-0040`

Snippet: `samples/tauceti/tauceti-0040.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.coproductUniqueIso_inv
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Products.lean
- **derivation**: coproductUniqueIso_inv (fun _ : PUnit.{u + 1} ↦ _root_.SheafOfModules.unit.{v₁, u₁, u} S)
- **proof_uses_it**: True
- **explanation**: Mathlib's `coproductUniqueIso_inv` (generated with `to_dual` from `productUniqueIso_hom`) states `(coproductUniqueIso f).inv = Sigma.ι f default` for `[Unique β] (f : β → C)`. The library defines `freePUnitIsoUnit S` as exactly `coproductUniqueIso (fun _ : PUnit ↦ unit S)`. Mathlib defines `ιFree i` as `Sigma.ι (fun _ ↦ unit R) i` and `free I` as `∐ (fun _ ↦ unit R)`. So the theorem is Mathlib's lemma with β := PUnit and f the constant family on `unit S`; since `default = PUnit.unit`, `Sigma.ι f default` is `ιFree PUnit.unit` once the definition is unfolded. The library's proof already applies this lemma directly.

### [`ContRepresentation.isUnitary_iff_norm_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean#L51-L58) — `tauceti-0058`

Snippet: `samples/tauceti/tauceti-0058.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.norm_map_iff_inner_map_map
- **file**: Mathlib/Analysis/InnerProductSpace/LinearMap.lean
- **derivation**: forall_congr' fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).symm
- **proof_uses_it**: True
- **explanation**: This is a special case of the Mathlib lemma. The library defines `IsUnitary π` as `∀ g v w, ⟪π g v, π g w⟫ = ⟪v, w⟫`. Mathlib's `LinearMap.norm_map_iff_inner_map_map` holds for any map `f` in a `LinearMapClass`. It states `(∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫)`. Taking `f := π g` and wrapping the result in `forall_congr'` over `g` (after `.symm`) gives the theorem exactly. All of the mathematical content (an inner-product-preserving linear map is the same as a norm-preserving one) is in the Mathlib lemma. The library's proof already applies it once in each direction.

### [`TauCeti.tsum_inner_mul_inner_hermiteFunctionLp`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Parseval.lean#L50-L55) — `tauceti-0074`

Snippet: `samples/tauceti/tauceti-0074.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HilbertBasis.tsum_inner_mul_inner
- **file**: Mathlib/Analysis/InnerProductSpace/l2Space.lean
- **derivation**: by simpa using (hermiteHilbertBasis 𝕜).tsum_inner_mul_inner f g
- **proof_uses_it**: True
- **explanation**: Mathlib's `HilbertBasis.tsum_inner_mul_inner` says that for any Hilbert basis `b` and any `x y`, `∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫`. This is Parseval's identity in polarized form. The library theorem is that lemma with `b := hermiteHilbertBasis 𝕜`, the library's own Hilbert basis of L²(ℝ; 𝕜). The only glue is `simpa`, which rewrites `hermiteHilbertBasis 𝕜 n` as `hermiteFunctionLp 𝕜 n`. The current proof is exactly this one line. The real new mathematics, that the Hermite functions form a Hilbert basis, lives in the library's definition `hermiteHilbertBasis`, not in this theorem. The statement itself is just Mathlib's Parseval identity instantiated at that basis, so the verdict is `special_case` and not `duplicate`. This is a judgement call: the "content lies in the library's own definitions" exclusion could be read as covering it, but the identity itself comes entirely from the Mathlib lemma.

### [`TauCeti.PathAlgebra.quadraticDualMk_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Quiver/PathAlgebra/Quadratic/Dual.lean#L222-L225) — `tauceti-0090`

Snippet: `samples/tauceti/tauceti-0090.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.mkₐ_eq_mk
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: by rw [quadraticDualMk, Ideal.Quotient.mkₐ_eq_mk]
- **proof_uses_it**: True
- **explanation**: The library defines `quadraticDualMk k Q R` as `Ideal.Quotient.mkₐ k (quadraticDualIdeal k Q R).asIdeal`. Mathlib's `Ideal.Quotient.mkₐ_eq_mk (I : Ideal A) [I.IsTwoSided] : ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I` gives the theorem once `I` is set to the library's ideal `(quadraticDualIdeal k Q R).asIdeal` and `A` to `(pathAlgebra k Q)ᵐᵒᵖ`, and the definition is unfolded. The current proof does exactly this. The theorem is just an unfolding lemma for the library's alias, so its only mathematical content is Mathlib's `rfl` lemma applied to one specific ideal. One could argue it is instead a definitional lemma about the library's own definition, which would make the verdict `none_found`; I chose `special_case` because `mkₐ_eq_mk` is a specific Mathlib lemma, not a general principle like `congrArg`.

### [`Submodule.sinThetaMap_self`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/InnerProductSpace/Projection/PrincipalAngle.lean#L159-L161) — `tauceti-0107`

Snippet: `samples/tauceti/tauceti-0107.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.IsOrtho.starProjection_comp_starProjection
- **file**: Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean
- **derivation**: (isOrtho_orthogonal_left U).starProjection_comp_starProjection
- **explanation**: The library defines `U.sinThetaMap V := Vᗮ.starProjection ∘L U.starProjection`, so `U.sinThetaMap U = 0` is `Uᗮ.starProjection ∘L U.starProjection = 0`. Mathlib's `IsOrtho.starProjection_comp_starProjection (h : U ⟂ V) : U.starProjection ∘L V.starProjection = 0` gives this with first submodule `Uᗮ` and second `U`. The hypothesis `Uᗮ ⟂ U` is `Submodule.isOrtho_orthogonal_left U`, and `Uᗮ.HasOrthogonalProjection` comes from the instance for orthogonal complements. The current proof uses the library's own `sinThetaMap_eq_zero_iff` instead. The derivation was not compiled and relies on `sinThetaMap` unfolding definitionally; otherwise put `rw [sinThetaMap]` first.

### [`AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/Normalization/Basic.lean#L60-L64) — `tauceti-0110`

Snippet: `samples/tauceti/tauceti-0110.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp
- **file**: Mathlib/AlgebraicGeometry/Normalization.lean
- **derivation**: f.normalizationDesc_comp (φ ≫ g.toNormalization) g.fromNormalization _
- **proof_uses_it**: True
- **explanation**: The library defines `normalizationMap g φ hφ` as `f.normalizationDesc (φ ≫ g.toNormalization) g.fromNormalization _`, so it is a direct wrapper around a Mathlib construction. Mathlib's `normalizationDesc_comp` says `f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization`. Taking `f₁ := φ ≫ g.toNormalization` and `f₂ := g.fromNormalization` gives exactly this theorem once the definition is unfolded. That unfolding is definitional, and any two proofs of the hypothesis `H` are equal, so the term should typecheck as written. I could not run Lean to confirm this; if plain elaboration does not see through the definition, `by simpa [normalizationMap] using …` is the fallback. The current proof, `simp [normalizationMap]`, unfolds the definition and then applies this lemma, which is tagged `@[simp]`. The real content (that the induced map lies over `J`) is Mathlib's, not the library's.

### [`TauCeti.QuiverRep.toVertex_ofVertex_of_ne`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Quiver/Representation/AsModule.lean#L334-L340) — `tauceti-0168`

Snippet: `samples/tauceti/tauceti-0168.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DirectSum.of_eq_of_ne
- **file**: Mathlib/Algebra/DirectSum/Basic.lean
- **derivation**: by rw [toVertex_apply, asModuleEquiv_ofVertex]; exact DirectSum.of_eq_of_ne v u z h
- **explanation**: This is a borderline call. In the library, `toVertex u` is defined as `DirectSum.component u ∘ asModuleEquiv`, and `ofVertex v` as `asModuleEquiv.symm ∘ DirectSum.lof v`. The library proves both unfolding lemmas, `toVertex_apply` and `asModuleEquiv_ofVertex`, by `rfl`. After unfolding, the goal is `component u (lof v z) = 0`. Both `component` and `lof` are definitionally the same as evaluating `DirectSum.of _ v z` at `u`. So the goal is exactly Mathlib's `DirectSum.of_eq_of_ne (i j) (x) (h : j ≠ i) : (of _ i x) j = 0`, with i := v, j := u, and `h : u ≠ v`. The derivation above was not compiled; it relies on the `component`/`lof` defeq closing the final `exact`.

The current proof gets the same result another way: it rewrites with `DirectSum.component.of` and then uses `dite_eq_right`. The only content beyond the library's thin wrapper definitions is "a single at index v, read at index u ≠ v, is zero", which is what Mathlib's lemma says. Hence special case and not duplicate. If wrapper lemmas about the library's own maps should count as library content, the verdict would be `none_found` instead.

### [`TauCeti.LocalCoefficientSystem.TwistedCubicalChain.induction_on`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Singular/Cubical/LocalCoefficients/Chains.lean#L141-L150) — `tauceti-0189`

Snippet: `samples/tauceti/tauceti-0189.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DirectSum.induction_on
- **file**: Mathlib/Algebra/DirectSum/Basic.lean
- **derivation**: refine DirectSum.induction_on x zero (fun c a ↦ ?_) add
simpa only [TwistedCubicalChain.ofCube] using ofCube c a
- **proof_uses_it**: True
- **explanation**: `TwistedCubicalChain L n` is an abbrev for `DirectSum (SingularCube X n) (fun c ↦ L.obj (FundamentalGroupoid.mk (c 0)))`, and `ofCube L c` is defined as `DirectSum.lof R _ _ c`, which unfolds to `DirectSum.of`. So the theorem is Mathlib's `DirectSum.induction_on` with `β` fixed to this coefficient family; the `of` case is restated through the library's `ofCube`. The library proof applies `DirectSum.induction_on` directly and closes the `of` case with a single rewrite. It is `special_case` rather than `duplicate` because Mathlib's lemma applies only after choosing this specific family.

### [`CategoryTheory.Sheaf.H.exact_δ_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Sites/SheafCohomology/LongExactSequence.lean#L84-L88) — `tauceti-0219`

Snippet: `samples/tauceti/tauceti-0219.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Sheaf.H.longSequence_exact₁'
- **file**: Mathlib/CategoryTheory/Sites/SheafCohomology/ExactSequences.lean
- **derivation**: (ShortComplex.ab_exact_iff_function_exact _).mp (longSequence_exact₁' hS n₀ n₁ h)
- **proof_uses_it**: True
- **explanation**: The match is `Sheaf.H.longSequence_exact₁'` in Mathlib. It says the short complex `ShortComplex.mk (ofHom (δ hS n₀ n₁ h)) (ofHom (map S.f n₁)) _` in `AddCommGrpCat` is exact. That is exactness of the long cohomology sequence at Hⁿ¹(F₁), the same mathematical content as the library theorem.

The library states it as `Function.Exact` of the underlying additive maps instead of categorical exactness. Mathlib's `ShortComplex.ab_exact_iff_function_exact` converts between the two forms with a single rewrite, and the library's proof does exactly that: it applies `longSequence_exact₁'` and rewrites. So the result is a one-line repackaging of the Mathlib lemma, not a new statement.

Since the two forms are logically equivalent rather than the same notation, I classed it as `special_case` instead of `duplicate`. I also checked `Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean` for a version already stated with `Function.Exact`. That file only has the categorical-exactness forms and the one-directional existence forms (`covariant_sequence_exact₁`, and `H.longSequence_exact₁` in the sheaf file). Neither of those is the full `Function.Exact` statement.

### [`TauCeti.DenseGraphLimits.SymmKernel.rectIntegral_eq_setIntegral_setIntegral`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Combinatorics/DenseGraphLimits/Kernel/Integral.lean#L77-L82) — `tauceti-0291`

Snippet: `samples/tauceti/tauceti-0291.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.setIntegral_prod
- **file**: Mathlib/MeasureTheory/Integral/Prod.lean
- **derivation**: rw [rectIntegral_def]
exact setIntegral_prod _ K.integrable_uncurry.integrableOn
- **proof_uses_it**: True
- **explanation**: `rectIntegral` is defined as `∫ p in S ×ˢ T, K p.1 p.2 ∂(μ.prod μ)`. Mathlib's `setIntegral_prod` says that for `f : α × β → E` integrable on `s ×ˢ t` with respect to `μ.prod ν`, `∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ`. The theorem is that lemma with `ν := μ`, `f := fun p => K p.1 p.2`, `s := S` and `t := T`, after unfolding the definition. The integrability hypothesis comes from the library's own lemma `K.integrable_uncurry`, used through `.integrableOn`; this is the only step that is not standard glue, but it is a one-term lookup. The mathematical content, Fubini on a rectangle, is all in `setIntegral_prod`. The library's current proof already uses this lemma, in exactly the two lines given here.

### [`TauCeti.CoveringSpace.proj_hom_comp_hom_left_hom`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Covering/Category.lean#L182-L186) — `tauceti-0299`

Snippet: `samples/tauceti/tauceti-0299.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Over.w
- **file**: Mathlib/CategoryTheory/Comma/Over/Basic.lean
- **derivation**: by rw [← TopCat.coe_comp, CategoryTheory.Over.w f.hom]
- **explanation**: `TauCeti.CoveringSpace X` is a reducible abbreviation for a full subcategory of Mathlib's `Over X` in `TopCat`, and `proj p` abbreviates `p.obj.hom`. A morphism `f : p ⟶ q` therefore has `f.hom : p.obj ⟶ q.obj` in `Over X`. Mathlib's `CategoryTheory.Over.w` (`φ.left ≫ g.hom = f.hom`) gives `f.hom.left ≫ q.proj = p.proj`. The theorem is this equation read as an equality of the underlying functions, and Mathlib's `TopCat.coe_comp` (`⇑(f ≫ g) = g ∘ f`, proved by `rfl`) is the only extra step. The library's proof rewrites with its own lemma `TauCeti.CoveringSpace.w`, which is `Over.w` restated. So it uses `Over.w` only indirectly, not by name. No elementwise `Over.w_apply` or similar exists in Mathlib.

### [`Ideal.rightTensorIdeal_iSup`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/TensorProduct/Ideal.lean#L154-L159) — `tauceti-0325`

Snippet: `samples/tauceti/tauceti-0325.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.map_iSup
- **file**: Mathlib/RingTheory/Ideal/Maps.lean
- **derivation**: Ideal.map_iSup (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom I
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Ideal.map_iSup`. The library defines `rightTensorIdeal R A I` as `Ideal.map (Algebra.TensorProduct.includeRight).toRingHom I`. `Ideal.map_iSup` says `(iSup K).map f = ⨆ i, (K i).map f` for any ring hom `f` between semirings. Taking `f` to be `includeRight.toRingHom` gives the theorem once the definition is unfolded, which is definitional. The library's current proof is exactly this application of `Ideal.map_iSup`.

### [`TauCeti.PresentedK0.map_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean#L394-L397) — `tauceti-0327`

Snippet: `samples/tauceti/tauceti-0327.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientAddGroup.map_mk
- **file**: Mathlib/GroupTheory/QuotientGroup/Defs.lean
- **derivation**: QuotientAddGroup.map_mk _ _ _ _ _
- **proof_uses_it**: True
- **explanation**: PresentedK0 rels is defined as the quotient FreeAbelianGroup (ObjectCode C) ⧸ AddSubgroup.closure rels. The library's mk is QuotientAddGroup.mk' and map F h is QuotientAddGroup.map (closure relsC) (closure relsD) (freeMap F) _. Once these definitions are unfolded, the lemma is QuotientAddGroup.map_mk (the additive form of QuotientGroup.map_mk, proved by rfl) with f := freeMap F; map_mk' states the same thing with mk'. The library's proof already applies this lemma. This is borderline: the lemma is the computation rule of the library's own wrapper map, but its whole content is Mathlib's computation rule for quotient maps.

### [`TauCeti.ClassFunction.characterPairing_ofFDRep_self`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/Pairing.lean#L257-L264) — `tauceti-0332`

Snippet: `samples/tauceti/tauceti-0332.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FDRep.char_orthonormal
- **file**: Mathlib/RepresentationTheory/Character.lean
- **derivation**: rw [characterPairing_ofFDRep]
simpa [if_pos (⟨CategoryTheory.Iso.refl V⟩ : Nonempty (V ≅ V))] using FDRep.char_orthonormal V V
- **explanation**: The library lemma `characterPairing_ofFDRep` rewrites `characterPairing (ofFDRep V) (ofFDRep W)` to `(Nat.card G : k)⁻¹ * ∑ g, V.character g * W.character g⁻¹`. This is exactly the left-hand side of Mathlib's `FDRep.char_orthonormal`, which states that this sum equals `if Nonempty (V ≅ W) then ↑1 else ↑0`. Mathlib's lemma needs the same assumptions as the theorem: `IsAlgClosed k`, `Fintype G`, `Invertible (Nat.card G : k)`, and `Simple V`, `Simple W`. Instantiating `W := V` makes the condition `Nonempty (V ≅ V)` true via `Iso.refl V`, so the right-hand side is 1. The current proof does not apply Mathlib's lemma directly. It goes through the library's `characterPairing_ofFDRep_orthonormal`, which is itself `characterPairing_ofFDRep` followed by `FDRep.char_orthonormal V W`.

### [`TauCeti.ClassData.sum_card_classFinset`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/Dixon/ClassData/Basic.lean#L366-L371) — `tauceti-0354`

Snippet: `samples/tauceti/tauceti-0354.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.card_eq_sum_card_fiberwise
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
- **derivation**: by simpa [classFinset] using (Finset.card_eq_sum_card_fiberwise (f := d.index) (s := Finset.univ) (t := Finset.univ) (by simp)).symm
- **proof_uses_it**: True
- **explanation**: `d.classFinset i` is defined as `{g | d.index g = i}`, which is the fiber of `d.index : G → Fin d.numClasses` over `i`, filtered from `univ`. Mathlib's `Finset.card_eq_sum_card_fiberwise` says `(H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}`. Taking `f := d.index` and `s = t = univ` (so `MapsTo` holds trivially), then flipping the equation with `.symm` and rewriting `#univ = Fintype.card G`, gives exactly the theorem. The library's proof already does this: it unfolds `classFinset`, rewrites with `Finset.card_univ`, and applies this lemma. I did not find a more specialized Mathlib lemma for sums over a `Fintype`. `Finset.sum_card_fiberwise_eq_card_filter` would also work, with a little more glue.

### [`QuadraticMap.IsometryEquiv.restrictProdRadicalOfIsCompl_symm_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/QuadraticForm/Radical.lean#L357-L366) — `tauceti-0388`

Snippet: `samples/tauceti/tauceti-0388.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.prodEquivOfIsCompl_symm_apply
- **file**: Mathlib/LinearAlgebra/Projection.lean
- **derivation**: change (W.prodEquivOfIsCompl Q.radical hW.symm).symm x = _
exact Submodule.prodEquivOfIsCompl_symm_apply hW.symm x
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. The library defines `IsometryEquiv.restrictProdRadicalOfIsCompl` with `toLinearEquiv := W.prodEquivOfIsCompl Q.radical hW.symm`, so the inverse of the isometry, applied to `x`, is by definition `(W.prodEquivOfIsCompl Q.radical hW.symm).symm x`. Mathlib's `Submodule.prodEquivOfIsCompl_symm_apply (hpq : IsCompl p q) (x : E)` states `(p.prodEquivOfIsCompl q hpq).symm x = (p.projectionOnto q hpq x, q.projectionOnto p hpq.symm x)`. With `p := W`, `q := Q.radical` and `hpq := hW.symm`, this is exactly the theorem's right-hand side, since `hW.symm.symm` is definitionally `hW`. The only glue is unfolding the library's wrapper with `change`, and the library's current proof does exactly this.

### [`TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.weightedAbelJacobiQuotientClass_eq_sum`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/WeilDivisor/AbelJacobi/Quotient.lean#L118-L138) — `tauceti-0402`

Snippet: `samples/tauceti/tauceti-0402.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finsupp.lift
- **file**: Mathlib/LinearAlgebra/Finsupp/LSum.lean
- **derivation**: exact (DFunLike.congr_fun ((Finsupp.lift _ ℤ X).apply_symm_apply (S.weightedAbelJacobiQuotientClass w hx₀).toIntLinearMap) D).symm
- **explanation**: In the library, `weightedAbelJacobiQuotientClass w hx₀` is an `AddMonoidHom` out of `WeilDivisor X`, which is defined as `X →₀ ℤ`, and `ofPoint x` is `Finsupp.single x 1`. The theorem therefore says that an additive map out of the free abelian group `X →₀ ℤ` is determined by its values on the generators: `F D = D.sum fun x n => n • F (single x 1)`.

Mathlib states this as the equivalence `Finsupp.lift M R X : (X → M) ≃+ ((X →₀ R) →ₗ[R] M)`. Its two simp lemmas are both proved by `rfl`:
- `Finsupp.lift_apply`: `lift f g = g.sum fun x r => r • f x`;
- `Finsupp.lift_symm_apply`: `(lift).symm f x = f (single x 1)`.

Take `R = ℤ` and turn the homomorphism into a linear map with `toIntLinearMap`. Applying `apply_symm_apply` to it and evaluating at `D` gives, up to definitional unfolding, exactly the claimed identity.

I did not compile the derivation. The term-mode `exact` relies on definitional unfolding: `lift_apply` and `lift_symm_apply` are `rfl`, `ofPoint x` is `single x 1`, and `toIntLinearMap` has the same underlying function. `simpa` would not work here, because simp would first simplify `lift (lift.symm F)` back to `F` and lose the needed form.

The library proves the result directly, by induction with `Finsupp.induction_linear`. I found no Mathlib lemma stating it in exactly this form for `Finsupp`. The closest are `MonoidAlgebra` analogues (`F f = f.coeff.sum fun a b => b • F (single a 1)`), but they do not apply to plain `X →₀ ℤ`.

The verdict is borderline. Most of the mathematical content sits in the `Finsupp.lift` equivalence, but the derivation also uses the general principle `apply_symm_apply`.

### [`TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.principalHom_injective_of_principalKernel_eq_bot`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/WeilDivisor/Principal/Kernel.lean#L82-L86) — `tauceti-0418`

Snippet: `samples/tauceti/tauceti-0418.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddMonoidHom.ker_eq_bot_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Ker.lean
- **derivation**: (AddMonoidHom.ker_eq_bot_iff S.principalHom).mp h
- **explanation**: The theorem is a special case. `principalKernel` is an `abbrev` for `S.principalHom.ker`. Mathlib's `MonoidHom.ker_eq_bot_iff (f : G →* M) : f.ker = ⊥ ↔ Function.Injective f` is tagged `@[to_additive]`, which generates `AddMonoidHom.ker_eq_bot_iff`. Taking `f := S.principalHom` and using `.mp` gives exactly the stated implication. The current proof goes through the library's own wrapper `principalKernel_eq_bot_iff`. That wrapper is just `AddMonoidHom.ker_eq_bot_iff S.principalHom`, so the proof uses the Mathlib lemma only indirectly, and I set `proof_uses_it` to false.

### [`TauCeti.normalizedValuation_eq_one_of_isOfFinOrder`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/LocalField/NormalizedValuation.lean#L239-L243) — `tauceti-0420`

Snippet: `samples/tauceti/tauceti-0420.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsOfFinOrder.eq_one'
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: ((normalizedValuation K).isOfFinOrder hx).eq_one'
- **proof_uses_it**: True
- **explanation**: In the library, `normalizedValuation K` is defined as a monoid hom `Kˣ →* Multiplicative ℤ`. Mathlib's `IsOfFinOrder.eq_one'` says that in a torsion-free group (`[IsMulTorsionFree G]`), any element of finite order equals 1. Here it is applied with G := Multiplicative ℤ and the element `normalizedValuation K x`. The finite-order hypothesis comes from the general fact that monoid homs preserve finite order (`MonoidHom.isOfFinOrder`), which counts as routine glue. The library's one-line proof is already exactly this. The only mathematical content is that a finite-order element of the torsion-free group ℤ is trivial, and that is Mathlib's lemma instantiated at a concrete group. I found no single Mathlib lemma combining both steps, e.g. "a hom into a torsion-free group kills torsion" (I searched for `torsion_le_ker`, `map_eq_one_of_isOfFinOrder` and similar names).

### [`Path.Homotopic.Quotient.subpath_zero_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Homotopy/Path.lean#L338-L343) — `tauceti-0445`

Snippet: `samples/tauceti/tauceti-0445.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Path.subpath_zero_one
- **file**: Mathlib/Topology/Subpath.lean
- **derivation**: by rw [Path.subpath_zero_one]; rfl
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Path.subpath_zero_one (γ : Path a b) : γ.subpath 0 1 = γ.cast γ.source γ.target`, moved into the homotopy quotient. In Mathlib, `Path.Homotopic.Quotient.mk_cast` (Mathlib/Topology/Homotopy/Path.lean) states `mk (P.cast hx hy) = (mk P).cast hx hy` and is proved by `rfl`. So after rewriting with `Path.subpath_zero_one`, the goal closes by `rfl` (the endpoint proofs agree by proof irrelevance). Equivalently, `congrArg mk (Path.subpath_zero_one p)` should work by definitional unfolding. All the mathematical content is in `Path.subpath_zero_one`, and the library's proof already rewrites with it. I did not find a quotient-level version of this statement in Mathlib. I searched for `subpath_zero_one` and for `subpath` together with `Quotient`; the only quotient-level subpath lemma is `mk_subpath_trans_mk_subpath`, which is a different statement. Neither suggested derivation has been compiled.

### [`TauCeti.ker_leftNumericalQuotientMk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/SesquilinearForm/NumericalQuotient/Basic.lean#L161-L164) — `tauceti-0448`

Snippet: `samples/tauceti/tauceti-0448.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.ker_mkQ
- **file**: Mathlib/LinearAlgebra/Quotient/Basic.lean
- **derivation**: (leftRadical b).ker_mkQ
- **proof_uses_it**: True
- **explanation**: This is a special case of `Submodule.ker_mkQ`. The library defines `leftNumericalQuotientMk b` as `(leftRadical b).mkQ`. Mathlib's `Submodule.ker_mkQ : ker p.mkQ = p` holds for any submodule `p`. Setting `p := leftRadical b` and unfolding that definition gives the theorem exactly, and the current proof is already this application.

### [`Finsupp.toLex_cons_lt_toLex_cons_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Finsupp/Fin.lean#L36-L41) — `tauceti-0467`

Snippet: `samples/tauceti/tauceti-0467.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Fin.pi_lex_lt_cons_cons
- **file**: Mathlib/Order/Fin/Tuple.lean
- **derivation**: simp only [Lex.lt_iff, ofLex_toLex]
exact Fin.pi_lex_lt_cons_cons (α := fun _ ↦ M) (s := fun {_} ↦ (· < ·))
- **proof_uses_it**: True
- **explanation**: This is a special case of `Fin.pi_lex_lt_cons_cons`. That lemma says `Pi.Lex (· < ·) s (Fin.cons x₀ x) (Fin.cons y₀ y) ↔ s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex … x y`, for dependent tuples and any relation `s`.

The library's theorem takes the constant family `α := fun _ ↦ M` and `s := (· < ·)`. It states the result for `Finsupp` in lex order rather than for plain functions. Mathlib's `Finsupp.Lex.lt_iff` holds by `rfl` and unfolds the lex `<` on finsupps into exactly that `Pi.Lex` form. Coercing `Finsupp.cons` to a function gives `Fin.cons` by definition.

So the only steps are a routine rewrite with these unfolding lemmas, followed by applying `Fin.pi_lex_lt_cons_cons` directly. The library's two-line proof already does exactly this. I found no Mathlib lemma stated directly for `Finsupp` lex order with `cons`: I searched `Data/Finsupp/Lex.lean` and grepped for `cons` together with `toLex` or `Lex` across Mathlib.

### [`TauCeti.continuous_restrictedProductCongrRight`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/RestrictedProduct/Congr/Right.lean#L120-L133) — `tauceti-0468`

Snippet: `samples/tauceti/tauceti-0468.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RestrictedProduct.mapAlong_continuous
- **file**: Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean
- **derivation**: by convert RestrictedProduct.mapAlong_continuous G H id Filter.tendsto_id (fun i ↦ φ i) (hφ.mono fun _ hi ↦ hi.mapsTo) hcont using 1; ext x i; simp
- **explanation**: Mathlib's `mapAlong_continuous` says that `mapAlong R₁ R₂ f hf φ hφ` is continuous when every coordinate map `φ j` is continuous. The underlying function of the library's `restrictedProductCongrRight U U' φ hφ` is `x ↦ ⟨fun i ↦ φ i (x i), _⟩`. That is the same function as `mapAlong G H id tendsto_id (fun i ↦ φ i) _`, which Mathlib also packages as `RestrictedProduct.map`. The match comes from taking `f = id`, using the cofinite filter on both sides, and weakening the `BijOn` hypothesis to its eventual `MapsTo` part. The two functions should even be definitionally equal, so a direct `exact` would probably also work. Mathlib has no bundled `congrRight` equivalence of restricted products, so this is a special case rather than a duplicate. The library's current proof goes through its own `continuous_restrictedProductMap` instead of citing Mathlib directly. I could not run Lean, so the derivation is untested.

### [`SymmetricAlgebra.gradedLift_ι`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/SymmetricAlgebra/GradedMap.lean#L62-L64) — `tauceti-0479`

Snippet: `samples/tauceti/tauceti-0479.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SymmetricAlgebra.lift_ι_apply
- **file**: Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean
- **derivation**: by rw [gradedLift_apply]; exact lift_ι_apply ((𝒜 1).subtype ∘ₗ f) m
- **proof_uses_it**: True
- **explanation**: This is a borderline call. `gradedLift R 𝒜 f` is defined as Mathlib's `SymmetricAlgebra.lift ((𝒜 1).subtype ∘ₗ f)`, packaged as a graded ring map. The library's `gradedLift_apply` states this, and it holds by `rfl`. Mathlib's `lift_ι_apply` says `lift g (ι R M a) = g a`. Take `g := (𝒜 1).subtype ∘ₗ f`. Then `g m` reduces by definition to `↑(f m)`, which is exactly the theorem. So the result is Mathlib's lemma with `g` fixed, after unfolding the library's definition. The current `simp` proof already goes this way: it rewrites with the simp lemma `gradedLift_apply` and then uses `lift_ι_apply`, which is also a simp lemma. The case for `none_found` instead: the statement is a basic API lemma for a definition the library made itself, and the instructions do not count results whose content lies in the library's own definitions. I chose `special_case` because the actual content, that the lift sends a generator to its image, is Mathlib's lemma.

### [`selfAdjoint.isHermitian_coe`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/SymmetricMatrix/Basic.lean#L201-L205) — `tauceti-0505`

Snippet: `samples/tauceti/tauceti-0505.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsSelfAdjoint.isHermitian
- **file**: Mathlib/LinearAlgebra/Matrix/Hermitian.lean
- **derivation**: IsSelfAdjoint.isHermitian A.2
- **explanation**: Mathlib's `IsSelfAdjoint.isHermitian : IsSelfAdjoint A → A.IsHermitian` is the `.mpr` direction of `Matrix.isHermitian_iff_isSelfAdjoint`, which is proved by `Iff.rfl`. It works for any square matrix over a type with `Star`. Being a member of `selfAdjoint.submodule ℝ _` unfolds by definition to `IsSelfAdjoint`, so `A.2` is the hypothesis this lemma needs. The library's theorem is therefore this lemma with real `Fin p × Fin p` matrices plugged in and the hypothesis read off the subtype membership. The library's own proof is just `A.2`, which relies on the same definitional unfolding and does not cite the lemma. The result has essentially no content beyond the definitions: it is the subtype projection combined with that `Iff.rfl`. I also checked `Mathlib/Algebra/Star/Module.lean` and found no lemma there that is stated directly for elements of `selfAdjoint.submodule` and concludes `IsHermitian`.

### [`TauCeti.heightLinearMap_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Height.lean#L70-L73) — `tauceti-0524`

Snippet: `samples/tauceti/tauceti-0524.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.Basis.coe_sumCoords
- **file**: Mathlib/LinearAlgebra/Basis/Defs.lean
- **derivation**: by rw [heightLinearMap, Module.Basis.coe_sumCoords]
- **proof_uses_it**: True
- **explanation**: This is a special case of `Module.Basis.coe_sumCoords`. The library's `heightLinearMap P b` is defined as `b.toWeightBasis.sumCoords`, so it is just another name for Mathlib's `Basis.sumCoords`. Mathlib's `Module.Basis.coe_sumCoords` says `(b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id` for any basis `b`. Taking `b := b.toWeightBasis` and unfolding the library definition gives the theorem exactly, and the current proof already does this with `rw [heightLinearMap, Module.Basis.coe_sumCoords]`. Mathlib's lemma itself holds by `rfl`. All the theorem contributes is unfolding the library's alias; the coordinate-sum formula comes from Mathlib.

### [`TauCeti.singularChainFiltrationIso_hom_comp_singularChainFiltrationι`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Singular/FilteredSpace.lean#L112-L118) — `tauceti-0528`

Snippet: `samples/tauceti/tauceti-0528.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk
- **file**: Mathlib/CategoryTheory/Subobject/Basic.lean
- **derivation**: Subobject.underlyingIso_hom_comp_eq_mk (singularChainFiltrationι R X q)
- **proof_uses_it**: True
- **explanation**: This is a special case of the Mathlib lemma. The Mathlib lemma states `(underlyingIso f).hom ≫ f = (mk f).arrow` for any mono `f`. The library defines `singularChainFiltration R X q := Subobject.mk (singularChainFiltrationι R X q)` and `singularChainFiltrationIso R X q := Subobject.underlyingIso (singularChainFiltrationι R X q)`. Unfolding these definitions, the theorem is the Mathlib lemma with `f := singularChainFiltrationι R X q`. The current proof already applies this lemma directly. The library definitions are thin wrappers around `Subobject.mk` and `underlyingIso`, so the theorem's actual content is the Mathlib lemma.

### [`Diffeomorph.fixingSubgroup_univ`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Diffeomorphism/FixingSubgroup/Basic.lean#L87-L90) — `tauceti-0564`

Snippet: `samples/tauceti/tauceti-0564.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MulAction.fixedBy_eq_univ_iff_eq_one
- **file**: Mathlib/GroupTheory/GroupAction/FixedPoints.lean
- **derivation**: by ext; simpa [_root_.mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one (α := M)
- **explanation**: Mathlib has no generic lemma `fixingSubgroup G Set.univ = ⊥` for a faithful action. I searched for `fixingSubgroup_univ`, `fixingSubgroup_eq_bot` and `fixingSubgroup … ⊥` in Mathlib, and found nothing for univ in GroupAction/FixingSubgroup.lean. The only matches are the Galois-specific `fixingSubgroup_top` lemmas, which do not apply here.

The content is in `MulAction.fixedBy_eq_univ_iff_eq_one`: under `[FaithfulSMul M α]`, `fixedBy α m = Set.univ ↔ m = 1`. Both statements reduce to `∀ x, g • x = x ↔ g = 1` once you unfold `mem_fixingSubgroup_iff` and `Subgroup.mem_bot`. Mathlib's `IsGaloisGroup.fixingSubgroup_top` gets the same result from this lemma with the one-liner `ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one`. My derivation copies that line, specialised to the diffeomorphism group acting on M; I could not compile it here.

The derivation also needs the `FaithfulSMul` instance for diffeomorphisms acting on M. I did not open the library's Action file to check, but the current proof uses `TauCeti.fixingSubgroup_univ`, which needs that instance, so it must be available. That library lemma is itself just this generic fact, proved by hand. So the current proof does not use the Mathlib declaration.

### [`TauCeti.Green.Division.integrableOn_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Green/Division/Basic.lean#L55-L59) — `tauceti-0577`

Snippet: `samples/tauceti/tauceti-0577.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.integrableOn_finset_iUnion
- **file**: Mathlib/MeasureTheory/Integral/IntegrableOn.lean
- **derivation**: by conv_lhs => rw [← V.covers]
   exact integrableOn_finset_iUnion
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `integrableOn_finset_iUnion` says `IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ`. Take `s := V.cells`, `t := fun K ↦ K.region d` and `μ := volume`, then use the structure field `V.covers : (⋃ K ∈ V.cells, K.region d) = D` to turn the union into `D`. That gives the theorem exactly. The library's current proof already does this, in two lines. The only content not taken from Mathlib is the covering field of the library's own `Division` structure.

### [`TopologicalAbelianization.map_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/Group/TopologicalAbelianization.lean#L120-L124) — `tauceti-0623`

Snippet: `samples/tauceti/tauceti-0623.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientGroup.map_mk
- **file**: Mathlib/GroupTheory/QuotientGroup/Defs.lean
- **derivation**: QuotientGroup.map_mk _ _ _ _ x
- **proof_uses_it**: True
- **explanation**: The library's `TopologicalAbelianization.map f hf` is defined as `QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)`. Mathlib's `TopologicalAbelianization G` is an abbrev for `G ⧸ (commutator G).topologicalClosure`. Once `map` is unfolded, the theorem is exactly Mathlib's `QuotientGroup.map_mk (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) : map N M f h ↑x = ↑(f x)`, with N and M taken to be the closed commutator subgroups. That lemma holds by `rfl`. The library's proof already applies it directly. Mathlib has no `TopologicalAbelianization.map`, so there is no exact duplicate. This is a borderline call: the statement is mainly the computation rule of the library's own wrapper definition. I classify it as `special_case` because all of its mathematical content comes from the generic Mathlib lemma.

### [`TauCeti.Subcomodule.coact_mem_tensor_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Coalgebra/Subcomodule/Basic.lean#L177-L185) — `tauceti-0647`

Snippet: `samples/tauceti/tauceti-0647.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.map_surjective
- **file**: Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean
- **derivation**: LinearMap.mem_range.mpr (TensorProduct.map_surjective (fun m ↦ ⟨⟨m, Submodule.mem_top⟩, rfl⟩) Function.surjective_id _)
- **proof_uses_it**: True
- **explanation**: TensorProduct.map_surjective (hg : Surjective g) (hg' : Surjective g') : Surjective (TensorProduct.map g g'), stated over a CommSemiring. The theorem instantiates g := (⊤ : Submodule R M).subtype, which is surjective via the anonymous constructor ⟨⟨m, mem_top⟩, rfl⟩, and g' := LinearMap.id, surjective by Function.surjective_id. It applies the result to the element Comodule.coact m and converts with LinearMap.mem_range.mpr. The comodule structure plays no role: coact m is just some element of M ⊗ C. The library's proof is exactly this one-line application. No Mathlib lemma states the range result directly; range_map and range_map_eq_span_tmul describe the range in other forms.

### [`TopPair.singularHomology_exact_space`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Singular/Relative.lean#L409-L412) — `tauceti-0666`

Snippet: `samples/tauceti/tauceti-0666.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SSetPair.homology_exact₂
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean
- **derivation**: (toSSetPair.obj P).homology_exact₂ R n
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `SSetPair.homology_exact₂`, and the library's proof already uses it. That lemma says that for any `P : SSetPair` and abelian coefficients `R`, the short complex `Hₙ(Y) ⟶ Hₙ(X) ⟶ Hₙ(X;Y)` is exact, with first map `SSet.homologyMap P.hom R n`, second map `P.homologyπ R n`, and the zero-composite proof `P.homologyMap_hom_homologyπ R n`.

In the library, `TopPair.singularHomology`, `TopPair.singularHomologyπ` and the relative chain complex are all abbrevs for the corresponding `SSetPair` constructions applied to `toSSetPair.obj P`. Here `toSSetPair` is the library's functor sending a topological pair to its pair of singular simplicial sets. It is defined so that `(toSSetPair.obj P).hom` is definitionally `TopCat.toSSet.map P.map`. So the TopPair statement is Mathlib's lemma with `P := toSSetPair.obj P`, up to unfolding definitions.

The exactness itself comes entirely from Mathlib; the library only adds the instantiation through its own functor `toSSetPair`.

### [`TauCeti.Huber.IsPseudoUniformizer.of_norm_lt_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RingTheory/Huber/Normed.lean#L103-L107) — `tauceti-0720`

Snippet: `samples/tauceti/tauceti-0720.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: tendsto_pow_atTop_nhds_zero_of_norm_lt_one
- **file**: Mathlib/Analysis/SpecificLimits/Normed.lean
- **derivation**: isPseudoUniformizer_iff.mpr ⟨hϖ, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1⟩
- **proof_uses_it**: True
- **explanation**: This is a borderline call. `IsPseudoUniformizer` is the library's own definition, and it unfolds by `Iff.rfl` to `IsUnit a ∧ IsTopologicallyNilpotent a`. The first half is just the hypothesis `hϖ`, passed through unchanged. The second half, `IsTopologicallyNilpotent ϖ`, unfolds to `Tendsto (ϖ ^ ·) atTop (𝓝 0)`. That is exactly the conclusion of Mathlib's `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, stated for any `[SeminormedRing R]` with `‖x‖ < 1`, which is the same setting as the theorem. So all of the mathematical content comes from that one Mathlib lemma, and the rest is unfolding a definition and building a pair, which is routine. The library's current proof is already this one-liner. It is not a strict duplicate: the conclusion also contains the trivial `IsUnit` part, and no arguments are instantiated, so the case does not fit either category exactly. I checked Mathlib's `TopologicallyNilpotent.lean` and found no Mathlib notion of pseudo-uniformizer, and no ready-made lemma saying that norm < 1 implies topologically nilpotent.

### [`TauCeti.Probability.coinKernel_apply_true`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Probability/Exchangeability/ConditionallyIID/CoinFlips.lean#L77-L81) — `tauceti-0724`

Snippet: `samples/tauceti/tauceti-0724.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem
- **file**: Mathlib/Probability/Distributions/Bernoulli.lean
- **derivation**: bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp)
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `bernoulliMeasure_apply_of_mem_of_notMem`. In the library, `coinKernel p` is defined as `⟨bernoulliMeasure true false p, _⟩`, and its underlying measure is `Ber(true, false, p)` by `rfl`. The Mathlib lemma says `Ber(x, y, p) s = toNNReal p` for a measurable set `s` with `x ∈ s` and `y ∉ s`. Taking `X = Bool`, `x = true`, `y = false` and `s = {true}` gives exactly the theorem, and the side conditions are routine (`measurableSet_singleton`, `rfl`, `simp`). The current proof only rewrites with the library's `rfl`-lemma `coinKernel_toMeasure` and then applies this lemma. Because of definitional unfolding, the one-line `exact` shown as the derivation should also work without that rewrite; this was not compiled, and if it fails, keep the `rw [coinKernel_toMeasure]` step.

### [`AlgebraicGeometry.Scheme.Hom.isIso_app_of_isBasis`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/Morphisms/Flat/StructureSheaf.lean#L60-L68) — `tauceti-0726`

Snippet: `samples/tauceti/tauceti-0726.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TopCat.Sheaf.isIso_iff_isIso_basis
- **file**: Mathlib/Topology/Sheaves/SheafCondition/Sites.lean
- **derivation**: have := TopCat.Sheaf.isIso_iff_isIso_basis (φ := (ObjectProperty.homMk p.c : X.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj Y.sheaf)) hB h
exact NatIso.isIso_app_of_isIso ((TopCat.Sheaf.forget _ _).map _) (op U)
- **proof_uses_it**: True
- **explanation**: Mathlib's TopCat.Sheaf.isIso_iff_isIso_basis says: for sheaves F G on X, a basis Opens.IsBasis (Set.range B) and φ : F ⟶ G, if every component φ.hom.app (op (B i)) is an isomorphism, then φ is an isomorphism. The library's theorem takes φ to be the structure-sheaf morphism p.c (as a morphism from X.sheaf to the pushforward of Y.sheaf), whose components on B i are p.app (B i). The lemma makes φ an isomorphism, and NatIso.isIso_app_of_isIso gives the component at op U. The forgetful-functor step should be found automatically (Functor.map_isIso is an instance); the two-line derivation has not been compiled, and if that instance is not found it needs the explicit `have` from the library's proof (three lines). The library's proof already does exactly this; the mathematical content is entirely the Mathlib lemma. No scheme-specific version was found in Mathlib/AlgebraicGeometry.

### [`AddSubgroup.natDegree_additivePolynomial`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Polynomial/AdditivePolynomial.lean#L80-L83) — `tauceti-0768`

Snippet: `samples/tauceti/tauceti-0768.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Lagrange.natDegree_nodal
- **file**: Mathlib/LinearAlgebra/Lagrange.lean
- **derivation**: by rw [additivePolynomial, Lagrange.natDegree_nodal, Finset.card_univ]
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma, and the current proof already uses it. The library defines `V.additivePolynomial` as exactly `Lagrange.nodal (Finset.univ : Finset V) (↑)`. Mathlib's `Lagrange.natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s` holds for any commutative ring `R`, any finset `s` and any map `v`. Taking `s = Finset.univ` and `v` to be the coercion `V → R` gives the theorem, once the definition is unfolded and `Finset.card_univ` is applied. The one-line proof does exactly this.

### [`PiLp.dist_le_sqrt_card_mul_dist_ofLp`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Normed/Lp/PiLp.lean#L132-L137) — `tauceti-0777`

Snippet: `samples/tauceti/tauceti-0777.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.lipschitzWith_toLp
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: by simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using (lipschitzWith_toLp 2 β).dist_le_mul (WithLp.ofLp x) (WithLp.ofLp y)
- **proof_uses_it**: True
- **explanation**: Mathlib's `PiLp.lipschitzWith_toLp` states `LipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@toLp p (∀ i, β i))`. Taking p = 2 makes the constant `card ι ^ (1/2) = √(card ι)`. The generic `LipschitzWith.dist_le_mul` turns this into the distance inequality, with `x`, `y` written as `toLp (ofLp x)`, `toLp (ofLp y)`. Only the rewrites `NNReal.coe_rpow` and `Real.sqrt_eq_rpow` are then needed. The library's proof does exactly this. Grepping Mathlib for `sqrt (Fintype.card` / `√(Fintype.card` turned up no lemma stating the √card bound directly.

### [`TauCeti.IntegralLattice.IntermediateCarrier.index_bot`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Index.lean#L148-L153) — `tauceti-0781`

Snippet: `samples/tauceti/tauceti-0781.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddSubgroup.relIndex_self
- **file**: Mathlib/GroupTheory/Index.lean
- **derivation**: by rw [index_def]; exact AddSubgroup.relIndex_self _
- **explanation**: This is a borderline call. The statement is about the library's own `index`, but once that definition is unfolded, the result is a direct instance of a Mathlib lemma.

By definition, `index M = relIndex ⊥ M = L.carrier.toAddSubgroup.relIndex M.1.toAddSubgroup` (this is `index_def`, proved by `rfl`). Intermediate carriers form the interval `Set.Icc L.carrier L.dualCarrier`, so the carrier of `⊥` is `L.carrier` (`Set.Icc.coe_bot`). So `index ⊥` is `H.relIndex H` with `H = L.carrier.toAddSubgroup`. The `@[to_additive]` lemma `AddSubgroup.relIndex_self : H.relIndex H = 1` (generated from `Subgroup.relIndex_self`, line 282) gives the result for that specific subgroup.

The derivation is untested (I can't run Lean). It relies on `(⊥ : L.IntermediateCarrier).1` reducing definitionally to `L.carrier`. If `exact` fails on that, adding `Set.Icc.coe_bot` to the `rw` should fix it.

The current proof does not call the Mathlib lemma directly. It goes through the library's `relIndex_bot_left` and `relIndex_self`, and the library's `relIndex_self` is itself proved by rewriting with `AddSubgroup.relIndex_self`.

### [`TauCeti.Contour.windingNumber_circle`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Contour/Winding/Number/Circle.lean#L121-L131) — `tauceti-0792`

Snippet: `samples/tauceti/tauceti-0792.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: circleIntegral.integral_sub_center_inv
- **file**: Mathlib/MeasureTheory/Integral/CircleIntegral.lean
- **derivation**: have h := circleIntegral.integral_sub_center_inv c hr; simp only [circleIntegral, smul_eq_mul, ← div_eq_mul_inv] at h
rw [h, inv_mul_cancel₀ Complex.two_pi_I_ne_zero]
- **explanation**: This is a special case of Mathlib's `circleIntegral.integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) : (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I`. The library's own docstring says as much.

`circleIntegral f c R` is defined as `∫ θ in 0..2π, deriv (circleMap c R) θ • f (circleMap c R θ)`. Unfolding it and rewriting `•` to `*` and then `* (z - c)⁻¹` to `/ (z - c)` gives exactly the integral in the theorem. That integral equals `2πi`, so the theorem's statement `(2πi)⁻¹ * ∫ ... = 1` follows by `inv_mul_cancel₀` (the library already uses `Complex.two_pi_I_ne_zero` for this elsewhere). Both statements have the same hypothesis, `r ≠ 0`.

I wrote the derivation by hand and could not compile it. The current proof goes another way: it specializes the library's own `indexIntegral_arc`, which computes the integrand as the constant `I`.

### [`TauCeti.asAlgebraHom_blockRepresentation`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/BlockRepresentation.lean#L96-L104) — `tauceti-0825`

Snippet: `samples/tauceti/tauceti-0825.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.lift_unique'
- **file**: Mathlib/Algebra/MonoidAlgebra/Basic.lean
- **derivation**: (MonoidAlgebra.lift_unique' (blockAlgHom e i)).symm
- **explanation**: This is a special case of `MonoidAlgebra.lift_unique'`. In Mathlib, `Representation.asAlgebraHom ρ` is defined as `MonoidAlgebra.lift k _ G ρ` (`asAlgebraHom_def` holds by `rfl`). The library defines `blockRepresentation e i` as `(blockAlgHom e i).toMonoidHom.comp (MonoidAlgebra.of k G)`. So the theorem says `lift k _ G ((blockAlgHom e i : k[G] →* _).comp (of k G)) = blockAlgHom e i`. That is the symmetric form of `MonoidAlgebra.lift_unique' (F : R[M] →ₐ[R] A) : F = lift R A M ((F : R[M] →* A).comp (of R M))` with `F := blockAlgHom e i`. The derivation only unfolds definitions: `asAlgebraHom` to `lift`, and `blockRepresentation` to the composite. These should be definitional equalities, but I could not check that `exact` closes the goal without running Lean. If it does not, `by rw [Representation.asAlgebraHom_def, blockRepresentation]; exact (MonoidAlgebra.lift_unique' _).symm` should work. The library's current proof does not use this lemma: it does an induction on `MonoidAlgebra` instead.

### [`IntermediateField.extendRight_le_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/FieldTheory/IntermediateField/ExtendRight.lean#L44-L54) — `tauceti-0837`

Snippet: `samples/tauceti/tauceti-0837.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.map_le_iff_le_comap
- **file**: Mathlib/FieldTheory/IntermediateField/Basic.lean
- **derivation**: map_le_iff_le_comap (f := Algebra.algHom K L M)
- **explanation**: This is a special case of `IntermediateField.map_le_iff_le_comap`. In Mathlib, `F.extendRight M` is defined as `F.map (Algebra.algHom K L M)`. Taking `f := Algebra.algHom K L M` in `map_le_iff_le_comap : s.map f ≤ t ↔ s ≤ t.comap f` gives `F.extendRight M ≤ E ↔ F ≤ E.comap (Algebra.algHom K L M)`. The two right-hand sides should agree by unfolding definitions. `F ≤ E.comap f` unfolds through `SetLike` to `∀ ⦃x⦄, x ∈ F → x ∈ E.comap f`. `comap` is built from `Subalgebra.comap`, so `x ∈ E.comap f` is definitionally `f x ∈ E`. Also, `Algebra.algHom K L M x` is definitionally `algebraMap L M x`. I could not run Lean, so I have not confirmed that the term elaborates exactly as written. If plain `exact` fails, it should go through with a `show`/`simp only [mem_comap]` step. The library proves the statement by hand through `map` and `mem_map` instead.

### [`TauCeti.proCCompletion.lift_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/Group/Profinite/ProC.lean#L332-L336) — `tauceti-0883`

Snippet: `samples/tauceti/tauceti-0883.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientGroup.lift_mk
- **file**: Mathlib/GroupTheory/QuotientGroup/Defs.lean
- **derivation**: QuotientGroup.lift_mk _ x
- **explanation**: This is a borderline case. `proCCompletion C G` is the quotient group `G ⧸ proCKernel C G`. The library defines `proCCompletion.lift hP f hf` directly as `QuotientGroup.lift (proCKernel C G) f (fun _ hx ↦ proCKernel_le_ker hP f hf hx)`, and the coercion `(x : proCCompletion C G)` is the quotient map. So once the library's definition is unfolded, the theorem is exactly Mathlib's `QuotientGroup.lift_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) : lift N φ HN (g : Q) = φ g`, with `N := proCKernel C G` and `φ := f`. Both are proved by `rfl`. The library's proof is just `rfl` and does not cite the Mathlib lemma. One could instead see this as a definitional computation rule of the library's own wrapper, with no mathematical content of its own; read that way, the verdict would be `none_found`.

### [`UniformSpace.Completion.continuous_mapRingEquiv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/UniformRing.lean#L133-L137) — `tauceti-0897`

Snippet: `samples/tauceti/tauceti-0897.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UniformSpace.Completion.continuous_map
- **file**: Mathlib/Topology/UniformSpace/Completion.lean
- **derivation**: continuous_map.congr fun x ↦ (mapRingEquiv_apply f hf hf' x).symm
- **proof_uses_it**: True
- **explanation**: This is a special case of `UniformSpace.Completion.continuous_map`, which says `Continuous (Completion.map f)` for any function `f`. Mathlib's `UniformSpace.Completion.mapRingEquiv` (in Mathlib/Topology/Algebra/UniformRing.lean) is built from `mapRingHom`, and `mapRingHom_apply` gives `mapRingHom f hf x = Completion.map f x`. So the underlying function of `mapRingEquiv f hf hf'` is `Completion.map ⇑f`, and its continuity is `continuous_map` with that function plugged in. The `simps` lemma `mapRingEquiv_apply` turns one form into the other. I checked Mathlib for a lemma stating continuity of `mapRingEquiv` or `mapRingHom` directly and found none. The library's proof already uses `continuous_map` this way, through `.congr` with the `simps` lemma, in one line.

### [`TauCeti.ConvexSubgroup.mem_maxAvoid_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Order/Group/ConvexSubgroup.lean#L372-L377) — `tauceti-0907`

Snippet: `samples/tauceti/tauceti-0907.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MulArchimedeanClass.mem_ballSubgroup_iff
- **file**: Mathlib/Algebra/Order/Archimedean/Class.lean
- **derivation**: MulArchimedeanClass.mem_ballSubgroup_iff (fun h ↦ hγ (MulArchimedeanClass.mk_eq_top_iff.mp h))
- **proof_uses_it**: True
- **explanation**: The library's `maxAvoid hγ` is just Mathlib's `MulArchimedeanClass.ballSubgroup (MulArchimedeanClass.mk γ)` repackaged as a convex subgroup; its carrier is exactly that ballSubgroup. Mathlib's `mem_ballSubgroup_iff (hA : c ≠ ⊤) : a ∈ ballSubgroup c ↔ c < mk a` already states the membership criterion. Taking `c := mk γ` gives the theorem. The side condition `mk γ ≠ ⊤` follows from `hγ` through `mk_eq_top_iff`. The library's proof is already this one-line application.

### [`TauCeti.invForm_apply_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/InvariantForm.lean#L126-L130) — `tauceti-0955`

Snippet: `samples/tauceti/tauceti-0955.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.BilinForm.apply_toDual_symm_apply
- **file**: Mathlib/LinearAlgebra/BilinearForm/Properties.lean
- **derivation**: LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) a _
- **proof_uses_it**: True
- **explanation**: I'm calling this a special case of Mathlib's lemma, though it's a borderline call. The library's `invForm` is just `LinearMap.BilinForm.congr (cartanEquivDual H) (traceForm K H L)`, and Mathlib defines `cartanEquivDual H` as `(traceForm K H L).toDual` together with the proof that the form is nondegenerate on `H`. So unfolding `invForm a b` gives `traceForm (e.symm a) (e.symm b)`, where `e = toDual`. Mathlib's `apply_toDual_symm_apply` states `B ((B.toDual hB).symm f) v = f v`. Taking `B := traceForm K H L`, `f := a` and `v := e.symm b` gives exactly the theorem. Only definitions are unfolded, and the library's current proof already applies this Mathlib lemma in one line. The borderline part: the statement is phrased with the library's own `invForm`, but all the mathematical content left after unfolding is Mathlib's generic fact about `toDual`, since `invForm` is just a thin wrapper.

### [`AlgEquiv.restrictNormal_eq_one_iff_algebraMap`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/FieldTheory/Galois/Restriction.lean#L204-L217) — `tauceti-0957`

Snippet: `samples/tauceti/tauceti-0957.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgEquiv.ker_restrictNormalHom
- **file**: Mathlib/FieldTheory/Galois/Basic.lean
- **derivation**: by change AlgEquiv.restrictNormalHom L σ = 1 ↔ _
   rw [← MonoidHom.mem_ker, AlgEquiv.ker_restrictNormalHom]; simp [IntermediateField.mem_fixingSubgroup_iff]
- **explanation**: Mathlib's `AlgEquiv.ker_restrictNormalHom` works in the same general tower setting: `F ⊆ E ⊆ K₁` with `[IsScalarTower F E K₁]` and `[Normal F E]`, where `E` is a type and not an intermediate field. It states that the kernel of `restrictNormalHom E : Gal(K₁/F) →* Gal(E/F)` is the fixing subgroup of the image of `E` in `K₁`.

The library theorem is the elementwise form of that statement: σ is in the kernel (`restrictNormalHom L σ = 1`, which is definitionally `σ.restrictNormal L = 1`) iff σ fixes every element of the image of `algebraMap L M`. The derivation:
- `change` rewrites the left side as `restrictNormalHom L σ = 1`;
- `MonoidHom.mem_ker` turns that into kernel membership;
- `ker_restrictNormalHom` replaces the kernel with the fixing subgroup;
- `simp` unfolds `mem_fixingSubgroup_iff` and `AlgHom.mem_fieldRange` / `IsScalarTower.coe_toAlgHom'`.

Mathlib's proof of `ker_restrictNormalHom` uses the same argument as the library's proof, via `restrictNormal_commutes` and injectivity of `algebraMap`.

Neither verdict fits exactly. The statements differ by more than notation (a kernel equality versus a pointwise iff), but no argument has to be instantiated, so this is closer to "duplicate" than a usual special case. I chose `special_case` because the gap is closed only by routine glue.

Caveat: I could not run Lean, so the derivation is untested. The final `simp` may need `AlgHom.mem_fieldRange` and `IsScalarTower.coe_toAlgHom'` added to its lemma list.

Mathlib also has `AlgEquiv.restrictNormal_eq_one_iff`, the same iff, but only for `L : IntermediateField F K₁`. It does not cover this setting.

### [`TauCeti.AlgebraicGeometry.WeilDivisor.EffectiveDivisorOfDegree.sup_le`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/WeilDivisor/Union.lean#L109-L114) — `tauceti-0982`

Snippet: `samples/tauceti/tauceti-0982.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sup_le
- **file**: Mathlib/Order/Lattice.lean
- **derivation**: by rw [coe_sup]; exact _root_.sup_le hDF hEF
- **proof_uses_it**: True
- **explanation**: I'm calling this a special case, but it's borderline. The library's `EffectiveDivisorOfDegree.sup D E` is a divisor chosen with `Classical.choose`. The library's own simp lemma `coe_sup` says that its coercion to `WeilDivisor X` is `↑D ⊔ ↑E`. After rewriting with `coe_sup`, the goal `↑D ⊔ ↑E ≤ F` is exactly Mathlib's lattice lemma `sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c`, with `a`, `b`, `c` taken in the lattice `WeilDivisor X`. The current proof already does this in two lines. Most of the content is Mathlib's `sup_le`. The only library-specific step is the `coe_sup` rewrite, which turns the library's `sup` into the lattice join. The case for `none_found` instead is that this rewrite uses a library lemma rather than plain unfolding, and the guidelines exclude theorems whose content lies in the library's own definitions.

### [`TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Basic.lean#L53-L56) — `tauceti-0991`

Snippet: `samples/tauceti/tauceti-0991.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.sqrt_ne_zero'
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: Real.sqrt_ne_zero'.mpr (by positivity)
- **explanation**: I found no Mathlib lemma about `√(n! * √π)` itself. The theorem follows from `Real.sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x` by taking `x = n! * √π`. The remaining side goal, `0 < (n! : ℝ) * √π`, is closed by `positivity`. This is a borderline case: the theorem is so routine that `by positivity` alone would probably prove it, so its content is close to trivial. The library's proof does not use this lemma. It goes through its own lemma `sqrt_factorial_mul_sqrt_pi_pos`, taking `.ne'` of it.

### [`TauCeti.TopBranchedCover.eq_extend`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/ThricePuncturedSphere/TopBranchedCover.lean#L614-L618) — `tauceti-0996`

Snippet: `samples/tauceti/tauceti-0996.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Dense.extend_unique
- **file**: Mathlib/Topology/DenseEmbedding.lean
- **derivation**: ContinuousMap.ext <| congrFun (X.dense_preimage_range.extend_unique hg g.continuous).symm
- **proof_uses_it**: True
- **explanation**: This is a special case of `Dense.extend_unique`. The library's `extend f hπ` is, by definition, the continuous map whose underlying function is `X.dense_preimage_range.extend (Subtype.val ∘ f)`. Mathlib's `Dense.extend_unique` says: if `hs : Dense s`, `g` is continuous with values in a T2 space, and `g x = f x` for every `x : s`, then `hs.extend f = g`.

Take `s = X.π ⁻¹' range toOnePoint`, use the library's density lemma `X.dense_preimage_range`, and plug in the given `g` and `hg`. This gives equality of the underlying functions. `ContinuousMap.ext` then lifts it to `g = extend f hπ`. The mathematical content of the theorem is exactly Mathlib's uniqueness of continuous extensions from a dense subset; the only extras are the library's wrapper definition and its density fact, passed in as arguments. The library's one-line proof already uses this lemma.

### [`TauCeti.measurePreserving_conj`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Group/Conjugation.lean#L98-L103) — `tauceti-0999`

Snippet: `samples/tauceti/tauceti-0999.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.measurePreserving_smul
- **file**: Mathlib/MeasureTheory/Group/Action.lean
- **derivation**: measurePreserving_smul (ConjAct.toConjAct h) μ
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `MeasureTheory.measurePreserving_smul`, and the library's proof already consists of that one application. Mathlib's lemma says that for `[SMul M α] [MeasurableConstSMul M α]` and `[SMulInvariantMeasure M α μ]`, the map `(c • ·)` preserves `μ`. The theorem takes `M := ConjAct G`, `α := G` and `c := ConjAct.toConjAct h`. The conjugation action `toConjAct h • g` unfolds by definition to `h * g * h⁻¹`, so Mathlib's statement becomes the theorem's statement. Mathlib's `MeasureTheory` directory contains no lemma specifically about measure-preservation under conjugation.


## Lean Pool (68 flagged)

### [`LeanPool.Monsky.valuation_max`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monsky/RainbowTriangles.lean#L173-L190) — `lean-pool-0001`

Snippet: `samples/lean-pool/lean-pool-0001.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valuation.map_sum_eq_of_lt
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: simpa [Fin.sum_univ_six] using v.map_sum_eq_of_lt (s := univ) (f := ![A, a₁, a₂, a₃, a₄, a₅]) (j := 0)
  (mem_univ _) (by intro i hi; fin_cases i <;> simp_all)
- **explanation**: The theorem is a special case of `Valuation.map_sum_eq_of_lt`, but this verdict is borderline. That lemma says: if `j ∈ s` and every other term has a smaller valuation (`∀ i ∈ s \ {j}, v (f i) < v (f j)`), then `v (∑ i ∈ s, f i) = v (f j)`.

To get the theorem, take `s = univ : Finset (Fin 6)`, `f = ![A, a₁, a₂, a₃, a₄, a₅]` and `j = 0`. The side condition comes down to the five hypotheses: split into cases with `fin_cases` and close each with `simp_all`. `Fin.sum_univ_six` turns the sum into `A + a₁ + a₂ + a₃ + a₄ + a₅`, which is the theorem's left-hand side. The lemma's typeclass assumptions (a ring and a `LinearOrderedCommGroupWithZero`) cover ℝ and Γ₀.

I could not compile the derivation, so it has not been checked. The current proof does not use this lemma. It chains the binary lemmas `Valuation.map_add_eq_of_lt_left` and `Valuation.map_add_lt` instead. The theorem adds nothing beyond fixing the sum at six terms, though the reduction relies on `fin_cases` and simp evaluation of the `![…]` vector.

### [`TauCeti.DavisKahanExt.starProjection_map_reflection`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/InfiniteDimensional/DoubleAngleSpectrum.lean#L475-L484) — `lean-pool-0007`

Snippet: `samples/lean-pool/lean-pool-0007.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.starProjection_map_apply
- **file**: Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean
- **derivation**: ext x; rw [Submodule.starProjection_map_apply]; rfl
- **proof_uses_it**: True
- **explanation**: This is a special case of `Submodule.starProjection_map_apply`. For a linear isometry equivalence `f` and a subspace `p`, that lemma says `(p.map f).starProjection x = f (p.starProjection (f.symm x))`. Take `f := V.reflection` and `p := U`; the codomain is `E` itself. The library's own definition `conjByIsometryEquiv W A` is `W ∘L A ∘L W.symm`, so after `ext x` the Mathlib lemma closes the goal, with `rfl` only unfolding that definition. The library's current proof already does exactly this. I found no operator-level (non-pointwise) form of the statement in Mathlib, so the verdict is special_case rather than duplicate.

### [`AVenhance.Infra.Parabolic.FourierGalerkin.Modes.mFourier_star_at`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/RealModes/Modes.lean#L139-L142) — `lean-pool-0010`

Snippet: `samples/lean-pool/lean-pool-0010.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UnitAddTorus.mFourier_neg
- **file**: Mathlib/Analysis/Fourier/AddCircleMulti.lean
- **derivation**: by rw [Complex.star_def]; exact UnitAddTorus.mFourier_neg.symm
- **proof_uses_it**: True
- **explanation**: Mathlib's `UnitAddTorus.mFourier_neg` says `mFourier (-n) x = conj (mFourier n x)` for any finite index type `d`. Here the library's `Torus` is defined as `UnitAddTorus (Fin 2)`, so the theorem is the case `d := Fin 2`. Its two sides are swapped, and it writes `star` where Mathlib writes `conj`; `Complex.star_def` rewrites one into the other. Because `d` has to be instantiated, the verdict is `special_case` rather than `duplicate`. The library's current proof already uses this lemma in the same way.

### [`CIV.abs_min_sub_min_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CIVAxisymmetric/Zoom/DriftExtraction.lean#L349-L354) — `lean-pool-0012`

Snippet: `samples/lean-pool/lean-pool-0012.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: abs_min_sub_min_le_max
- **file**: Mathlib/Algebra/Order/Group/MinMax.lean
- **derivation**: by simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))] using abs_min_sub_min_le_max a c b c
- **explanation**: The Mathlib lemma `abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| ≤ max |a - c| |b - d|` holds in any linearly ordered additive commutative group. Taking ℝ for α and the arguments (a, c, b, c) gives `|min a c - min b c| ≤ max |a - b| |c - c|`. Here |c - c| = 0, so the max simplifies to |a - b|. This is exactly how Mathlib proves the max version, `abs_max_sub_max_le_abs`, from `abs_max_sub_max_le_max` in the same file. Mathlib has no min analogue of that lemma (`abs_min_sub_min_le_abs`): I searched for `min_sub_min` names and for `|min _ _ - min _ _| ≤ |`. The library's current proof uses `lipschitzWith_min` instead.

### [`LeanPolyABC.prime_dvd_radical_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanPolyABC/Lib/Radical.lean#L120-L128) — `lean-pool-0027`

Snippet: `samples/lean-pool/lean-pool-0027.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible
- **file**: Mathlib/RingTheory/Radical/Basic.lean
- **derivation**: UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.irreducible ha
- **explanation**: The theorem is already in Mathlib. Mathlib's `dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b ≠ 0) : a ∣ radical b ↔ a ∣ b` is stated under the same typeclass assumptions as the library: `CommMonoidWithZero`, `NormalizationMonoid` and `UniqueFactorizationMonoid`.

- **Hypothesis:** Mathlib assumes `Irreducible`, which is weaker than the library's `Prime` hypothesis. `hp.irreducible` supplies it.
- **The `radical` definition:** the library uses its own `LeanPolyABC.radical`, but it is a verbatim copy of Mathlib's `UniqueFactorizationMonoid.radical`. Both are `(primeFactors a).prod id`, where `primeFactors a = (normalizedFactors a).toFinset` is defined under `open scoped Classical`. So the two definitions should be definitionally equal by unfolding. I could not run Lean to confirm that the one-line term above type-checks.

The mathematical content (an irreducible or prime element divides the radical of `a` iff it divides `a`) is exactly Mathlib's lemma. The library's proof follows the same argument, using `exists_mem_normalizedFactors_of_dvd` and `Finset.dvd_prod_of_mem`, but it does not cite this lemma.

### [`CIV.polarR_eq_zero_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CIVAxisymmetric/Closure/PolarREqZero.lean#L28-L44) — `lean-pool-0039`

Snippet: `samples/lean-pool/lean-pool-0039.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sq_add_sq_eq_zero
- **file**: Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean
- **derivation**: by rw [polarR, Real.sqrt_eq_zero (by positivity), sq_add_sq_eq_zero]
- **explanation**: The library defines `polarR x` as `Real.sqrt (x 0 ^ 2 + x 1 ^ 2)`. Mathlib's `sq_add_sq_eq_zero : a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0` holds in any linearly ordered ring. With `a := x 0` and `b := x 1` it gives the theorem's mathematical content. The only other step is removing the square root, which is a routine rewrite with `Real.sqrt_eq_zero` (side goal `0 ≤ x 0 ^ 2 + x 1 ^ 2` closed by `positivity`). The current proof does the same thing by hand with `Real.sqrt_eq_zero'`, `linarith`/`nlinarith` and `sq_eq_zero_iff`. I have not compiled the suggested one-line derivation.

### [`CIV.volume_axis_eq_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CIVAxisymmetric/Closure/AxisMeasureZero.lean#L33-L47) — `lean-pool-0062`

Snippet: `samples/lean-pool/lean-pool-0062.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.pi_hyperplane
- **file**: Mathlib/MeasureTheory/Constructions/Pi.lean
- **derivation**: measure_mono_null (fun _ hx => hx.1) (Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) 0 0)
- **explanation**: Here Vec3 is `Fin 3 → ℝ`, and its `volume` unfolds to `Measure.pi (fun _ => volume)`. Mathlib's `Measure.pi_hyperplane μ i x : Measure.pi μ {f | f i = x} = 0` holds whenever each factor has `NullSingletonClass`. Taking i = 0 and x = 0 shows the plane {x | x 0 = 0} is null. The axis {x | x 0 = 0 ∧ x 1 = 0} lies inside it, so `measure_mono_null` finishes the proof. This counts as special_case only if `measure_mono_null` is treated as routine glue; it is not on the listed glue, so the call is borderline. The library's proof instead builds the axis by hand as a proper submodule and applies `Measure.addHaar_submodule`, which is much longer. No Mathlib lemma states the exact two-coordinate set.

### [`Demazure.transposition_commutes_adjacent'`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DemazureOperatorsLean/DemazureAuxRelations.lean#L181-L191) — `lean-pool-0100`

Snippet: `samples/lean-pool/lean-pool-0100.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.swap_mul_swap_mul_swap
- **file**: Mathlib/Algebra/Group/End.lean
- **derivation**: have := (Equiv.swap_mul_swap_mul_swap (x := (⟨i+2, h2⟩ : Fin (n+1))) (y := ⟨i+1, h1⟩) (z := ⟨i, h0⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])).trans ((Equiv.swap_comm _ _).trans (Equiv.swap_mul_swap_mul_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])).symm)
rw [Equiv.swap_comm ⟨i+1, h1⟩ ⟨i, h0⟩, Equiv.swap_comm ⟨i+2, h2⟩ ⟨i+1, h1⟩] at this; exact congrArg (⇑) this
- **explanation**: The theorem is the braid relation for the transpositions a=⟨i⟩, b=⟨i+1⟩, c=⟨i+2⟩, stated for composed functions: (a b)(b c)(a b) = (b c)(a b)(b c). Mathlib's `Equiv.swap_mul_swap_mul_swap` (x ≠ y, x ≠ z ⊢ swap y z * swap x y * swap y z = swap z x) handles both sides. With (x,y,z)=(c,b,a) the left side becomes swap a c. With (x,y,z)=(a,b,c) the right side becomes swap c a, which equals swap a c by `swap_comm`. Two more `swap_comm` rewrites put the left side in the theorem's form, and coercing to functions finishes. The distinctness side goals compare ↑i, ↑i+1 and ↑i+2 and should close with simp [Fin.ext_iff]. This is borderline: no Mathlib lemma states the braid relation directly, and the derivation (two applications plus several swap_comm rewrites) is closer to three lines than two, so a strict reading of the two-line limit would give none_found. The derivation was not compiled. The library proves the result through its own pointwise lemma, by case analysis.

### [`Zeta32.Analytic.EnergyI.uC_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta32/Analytic/Energy/CIntegrals.lean#L121-L122) — `lean-pool-0116`

Snippet: `samples/lean-pool/lean-pool-0116.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.sqrt_sq
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: by unfold uC; simp [Real.sqrt_sq ha.le]
- **proof_uses_it**: True
- **explanation**: This is a special case of `Real.sqrt_sq`. The library defines `uC a c := √(c^2 + a^2)`, so `uC a 0 = a` unfolds to `√(0^2 + a^2) = a`. After `simp` removes the `0^2 +` term, this is exactly `Real.sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x` with `x := a`, using `ha.le` for the hypothesis. The library's current proof already does this.

### [`SteinhausThreeGap.posOrbit_nonempty`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SteinhausThreeGap/Basic.lean#L235-L241) — `lean-pool-0139`

Snippet: `samples/lean-pool/lean-pool-0139.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.Nontrivial.erase_nonempty
- **file**: Mathlib/Data/Finset/Basic.lean
- **derivation**: (Finset.one_lt_card_iff_nontrivial.mp (by unfold orbitCard at h2; omega)).erase_nonempty
- **explanation**: The theorem is a special case of `Finset.Nontrivial.erase_nonempty`. In the library, `posOrbit a N` is defined as `(orbit a N).erase 0` and `orbitCard a N` as `(orbit a N).card`. Unfolded, the theorem says that if a finset has at least 2 elements, then erasing 0 from it leaves a nonempty finset. Mathlib's lemma states `s.Nontrivial → (s.erase a).Nonempty`; here `s := orbit a N` and `a := 0`. The standard glue lemma `Finset.one_lt_card_iff_nontrivial` (Mathlib/Data/Finset/Card.lean) turns `2 ≤ card` into `Nontrivial`. The library's current proof uses that same glue lemma, then proves the erase step by hand with `exists_ne` instead of citing `erase_nonempty`. The suggested derivation was not compiled.

### [`BooleanIsoperimetry.CoherentGap.dot_sub`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L492-L495) — `lean-pool-0144`

Snippet: `samples/lean-pool/lean-pool-0144.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sub_dotProduct
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by unfold dot; exact sub_dotProduct first second weights
- **explanation**: The library defines `Relation n := Fin n → ℤ` and `dot relation weights := ∑ i, relation i * weights i`. This is definitionally Mathlib's `dotProduct` (`∑ i, v i * w i`) with index type `Fin n` and ring `ℤ`. Mathlib's `sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w` holds for any NonUnitalNonAssocRing. Taking the ring to be ℤ and the index type to be Fin n, and unfolding `dot`, gives exactly the library's lemma. The current proof re-proves it with `simp [dot, sub_mul, Finset.sum_sub_distrib]` and does not use the Mathlib lemma. The suggested derivation was not compiled.

### [`gcd_reduction_pos_a_div`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RamanujanTauMissesPrimes/Solution.lean#L3109-L3111) — `lean-pool-0188`

Snippet: `samples/lean-pool/lean-pool-0188.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Nat.div_gcd_pos_of_pos_left
- **file**: Init/Data/Nat/Gcd.lean
- **derivation**: Nat.div_gcd_pos_of_pos_left b ha
- **explanation**: Lean core has `theorem Nat.div_gcd_pos_of_pos_left (b : Nat) (h : 0 < a) : 0 < a / a.gcd b`. This is the same statement as `0 < a / Nat.gcd a b` given `0 < a`, with only the argument order and implicitness different. The library's proof does not apply it; it combines `Nat.div_pos`, `Nat.le_of_dvd` and `Nat.gcd_pos_of_pos_left` instead.

### [`NavierStokesR3.LocalizedTensorBounds.continuous_component`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/R3/PressureFlux.lean#L2383-L2385) — `lean-pool-0195`

Snippet: `samples/lean-pool/lean-pool-0195.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.continuous_apply
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: (PiLp.continuous_apply _ _ i).comp hf
- **explanation**: In the library, `Space` is an abbreviation for `EuclideanSpace ℝ (Fin 3)`, which is `PiLp 2 (fun _ => ℝ)`. Mathlib's `PiLp.continuous_apply (p) (β) (i) : Continuous (fun f : PiLp p β ↦ f i)` says that taking the i-th coordinate of a `PiLp` point is continuous. The theorem takes `p = 2`, `β = fun _ => ℝ` and composes this with `hf`, using only `Continuous.comp`. That gives `Continuous (fun x => f x i)`. `PiLp.continuous_apply` carries the theorem's mathematical content. The library's current proof does not use it: it rebuilds the same fact by hand from `EuclideanSpace.equiv` and the generic `continuous_apply`. The lemma is tagged `fun_prop`, so `by fun_prop` should also close the goal.

### [`EulerOrdinaryMollifier.kernel_compact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerLocalExistence.lean#L644-L644) — `lean-pool-0216`

Snippet: `samples/lean-pool/lean-pool-0216.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContDiffBump.hasCompactSupport_normed
- **file**: Mathlib/Analysis/Calculus/BumpFunction/Normed.lean
- **derivation**: (bump n).hasCompactSupport_normed
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `ContDiffBump.hasCompactSupport_normed`. In the library, `kernel n` is defined as `(bump n).normed volume`, where `bump n` is a specific `ContDiffBump` centred at 0 on `Space`. Mathlib's lemma says `HasCompactSupport (f.normed μ)` for any bump function `f` and measure `μ`. Taking `f := bump n` and `μ := volume` gives the theorem once `kernel` is unfolded. The library's proof is exactly this one-line application.

### [`AleksandrovDifferentiability.secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L314-L321) — `lean-pool-0234`

Snippet: `samples/lean-pool/lean-pool-0234.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.ae_iff
- **file**: Mathlib/MeasureTheory/OuterMeasure/AE.lean
- **derivation**: ae_iff (p := SecondOrderDifferentiableAt u)
- **proof_uses_it**: True
- **explanation**: I found that this theorem is Mathlib's `ae_iff` instantiated at `p := SecondOrderDifferentiableAt u`. `ae_iff` states `(∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0` and is proved by `Iff.rfl`.

Two library definitions are involved:
- `SecondOrderDifferentiableAE μ u` is by definition `∀ᵐ x ∂μ, SecondOrderDifferentiableAt u x`.
- `secondOrderBadSet u` is the complement of `secondOrderDifferentiabilitySet u`, which the library's proof shows is equal by `rfl` to `{x | ¬ SecondOrderDifferentiableAt u x}`.

So the instantiated `ae_iff` should typecheck against the theorem up to unfolding these definitions. I haven't compiled the derivation. If elaboration doesn't see through the definitions, `by rw [SecondOrderDifferentiableAE, ae_iff]; rfl` should work instead.

The library's current proof already applies `ae_iff`. All it adds is the `rfl` set identification.

One caveat on the verdict: `ae_iff` holds by definition, so the theorem is close to a pure restatement of the library's own definitions. That makes `special_case` a borderline call.

### [`Feige.CalibratedChain.sum_chainMass_shift`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Feige/ChainCalibration.lean#L60-L68) — `lean-pool-0235`

Snippet: `samples/lean-pool/lean-pool-0235.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.sum_range_sub'
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
- **derivation**: by simpa [chainMass, add_assoc] using Finset.sum_range_sub' (fun j => K (t + j)) r
- **explanation**: `Finset.sum_range_sub'` is the additive form of `Finset.prod_range_div'`, produced by `to_additive`. It states: ∑ i ∈ range n, (f i - f (i + 1)) = f 0 - f n, for any commutative additive group.

The library defines `chainMass K j` as `K j - K (j + 1)`. Take f := fun j => K (t + j) and n := r. The lemma's left side becomes ∑ j ∈ range r, (K (t + j) - K (t + (j + 1))), which is the theorem's sum after `add_assoc`. Its right side becomes K (t + 0) - K (t + r), and `simp` turns t + 0 into t.

The library proves the result by its own induction on r and does not use this lemma. I could not compile the one-line derivation, but the two sides should already agree up to definitional unfolding.

### [`MetricCodes.Johnson.coordinateSplitEquiv_card`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MetricCodes/Binary.lean#L979-L988) — `lean-pool-0264`

Snippet: `samples/lean-pool/lean-pool-0264.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.card_toLeft_add_card_toRight
- **file**: Mathlib/Data/Finset/Sum.lean
- **derivation**: change #((coordinateSumEquiv x).symm.finsetCongr S).toLeft + #((coordinateSumEquiv x).symm.finsetCongr S).toRight = #S
rw [Finset.card_toLeft_add_card_toRight]; simp
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of the Mathlib lemma, though only just. `coordinateSplitEquiv x` is defined as `(coordinateSumEquiv x).symm.finsetCongr.trans Finset.sumEquiv.toEquiv`, and `Finset.sumEquiv` sends `u` to `(u.toLeft, u.toRight)`. So once the definition is unfolded, the left-hand side is `#u.toLeft + #u.toRight` with `u := (coordinateSumEquiv x).symm.finsetCongr S`. Mathlib's `Finset.card_toLeft_add_card_toRight` (`#u.toLeft + #u.toRight = #u`) rewrites this to `#u`. What remains, `#(S.map e.toEmbedding) = #S`, is closed by `simp` using `Equiv.finsetCongr_apply` and `Finset.card_map`. The library's proof already does exactly this: it unfolds with `change`, rewrites with that lemma, and finishes with `simp`. The suggested derivation follows the same steps but has not been compiled. This is a borderline call: the result also relies on the library's own definition `coordinateSplitEquiv`, but that definition is only a composition of Mathlib equivalences. The mathematical content, that the left and right parts of a finset of a sum type add up to its cardinality, is Mathlib's lemma, applied to one particular finset.

### [`QuantumQueryComplexity.isSelfAdjoint_chordSq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuantumQuery/StateConversion.lean#L407-L410) — `lean-pool-0288`

Snippet: `samples/lean-pool/lean-pool-0288.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsSelfAdjoint.star_mul_self
- **file**: Mathlib/Algebra/Star/SelfAdjoint.lean
- **derivation**: IsSelfAdjoint.star_mul_self (1 - U)
- **explanation**: The library defines `chordSq U := (1 - U)ᴴ * (1 - U)`. For matrices, `star` is by definition `conjTranspose` (`Matrix.star_eq_conjTranspose` holds by `rfl`), so `chordSq U` is definitionally `star (1 - U) * (1 - U)`. Mathlib's `IsSelfAdjoint.star_mul_self (x : R) : IsSelfAdjoint (star x * x)` applied with `x := 1 - U` therefore gives the theorem directly; once `chordSq` is unfolded, the result is just the fact that `star x * x` is self-adjoint. `Matrix.isHermitian_conjTranspose_mul_self (1 - U)` would also work, since `IsHermitian` unfolds to `IsSelfAdjoint`. The current proof takes another route: it uses the library's own lemma `chordSq_conjTranspose`, which it proves by rewriting with `conjTranspose_mul`. I could not run Lean, so the one-line derivation is unchecked; it relies on Lean unfolding `chordSq` and matrix `star` automatically. If that fails, `by unfold chordSq; exact IsSelfAdjoint.star_mul_self (1 - U)` should work.

### [`EulerPacketInductionScales.Scales.support_pos`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketInductionScaleBounds.lean#L53-L53) — `lean-pool-0308`

Snippet: `samples/lean-pool/lean-pool-0308.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.exp_pos
- **file**: Mathlib/Analysis/Complex/Exponential.lean
- **derivation**: exp_pos _
- **proof_uses_it**: True
- **explanation**: This is a special case of `Real.exp_pos`. The library defines `supportScale J X n` as `exp (-scaleSequence J X n / ((J+n : ℕ) : ℝ)^(7/2 : ℝ))` (in `PacketSourceScaleSequence.lean`). Once that definition is unfolded, the theorem is `Real.exp_pos (x : ℝ) : 0 < exp x` applied to this particular argument, and the current proof is exactly `exp_pos _`. Nothing else in the result goes beyond the library's definition of `supportScale`.

### [`EulerCylinderMollifier.mollifierKernel_integral`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/Foundations/CylinderMollifier.lean#L95-L96) — `lean-pool-0333`

Snippet: `samples/lean-pool/lean-pool-0333.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContDiffBump.integral_normed
- **file**: Mathlib/Analysis/Calculus/BumpFunction/Normed.lean
- **derivation**: (mollifierBump n).integral_normed
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `ContDiffBump.integral_normed`, and the current proof already applies that lemma directly. The Mathlib lemma states `∫ x, f.normed μ x ∂μ = 1` for any bump function `f : ContDiffBump c` and any suitable measure `μ`. The library's `mollifierKernel n` is defined as `(mollifierBump n).normed volume`. So the theorem is that lemma with `f := mollifierBump n`, a concrete bump centred at 0 in `Domain 4`, and `μ := volume`. Because it needs these specific arguments rather than restating the general result, the verdict is special case, not duplicate.

### [`LeanStationaryHarmonicMaps.StationaryHarmonicMap.deriv_thetaFactor`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanStationaryHarmonicMaps/StationaryHarmonicMap/EnergyQuantities.lean#L103-L112) — `lean-pool-0370`

Snippet: `samples/lean-pool/lean-pool-0370.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: deriv_zpow
- **file**: Mathlib/Analysis/Calculus/Deriv/ZPow.lean
- **derivation**: unfold thetaFactor; rw [deriv_zpow, show (2 - (n:ℤ)) - 1 = 1 - (n:ℤ) by omega]; push_cast; ring
- **proof_uses_it**: True
- **explanation**: thetaFactor n r is defined as r ^ (2 - (n:ℤ)). Mathlib's deriv_zpow (m : ℤ) (x : 𝕜) states deriv (fun x => x ^ m) x = m * x ^ (m - 1), with no hypothesis on x. Taking 𝕜 = ℝ and m = 2 - n gives the theorem. The only glue needed is the integer cast ((2 - n : ℤ) : ℝ) = 2 - n and the exponent identity (2 - n) - 1 = 1 - n, closed by omega. The library's proof already applies deriv_zpow. The suggested derivation has not been compiled.

### [`EllipticPdes.Extension.stepProfile_le_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EllipticPDE/Extension/Cutoff.lean#L62-L62) — `lean-pool-0373`

Snippet: `samples/lean-pool/lean-pool-0373.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.smoothTransition.le_one
- **file**: Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean
- **derivation**: Real.smoothTransition.le_one (t - 1)
- **proof_uses_it**: True
- **explanation**: The library defines `stepProfile t := Real.smoothTransition (t - 1)`, and the theorem states `stepProfile t ≤ 1`. Mathlib's `Real.smoothTransition.le_one (x : ℝ) : smoothTransition x ≤ 1` (line 188 of that file) gives this directly: set `x := t - 1` and unfold the definition. The library's proof is already exactly this application. The bound itself comes from Mathlib's lemma; the library only adds a wrapper with a shifted argument. That makes this a special case, not a duplicate.

### [`Nat.gt_and_neq_succ_gt_succ`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MRiscX/Util/BasicTheorems.lean#L68-L70) — `lean-pool-0409`

Snippet: `samples/lean-pool/lean-pool-0409.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.lt_of_le_of_ne
- **file**: Init/Prelude.lean
- **derivation**: fun n m h₁ h₂ => Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h₁) (Ne.symm h₂)
- **explanation**: This is a special case. Lean core's `Nat.lt_of_le_of_ne : n ≤ m → n ≠ m → n < m` gives the result with its first argument set to `n + 1`. On ℕ, `n < m` is definitionally `n + 1 ≤ m`; `Nat.succ_le_of_lt` states that step explicitly, and `h₁` alone may also work. The hypothesis `m ≠ n + 1` just has to be flipped with `Ne.symm`. The library's proof uses `grind` and does not cite this lemma. I did not compile the derivation. I also searched for a lemma stating the result directly (names like `succ_lt_of_*`, `add_one_lt_of_*`, `lt_of_lt_of_ne`, and `Order.succ_lt_*`) and found none.

### [`BollobasNikiforov.euclid_sq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BollobasNikiforov/M/HalfPlane.lean#L59-L60) — `lean-pool-0416`

Snippet: `samples/lean-pool/lean-pool-0416.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.sq_sqrt
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: Real.sq_sqrt (by simpa using Matrix.dotProduct_self_star_nonneg w)
- **proof_uses_it**: True
- **explanation**: The library defines `euclid w := Real.sqrt (w ⬝ᵥ w)`, so the theorem is just `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x` with `x := w ⬝ᵥ w`. The library's proof already applies `Real.sq_sqrt` directly. The side condition `0 ≤ w ⬝ᵥ w` comes from the library's helper `euclid_inner_nonneg`. On ℝ, Mathlib's `Matrix.dotProduct_self_star_nonneg` gives the same fact once `star` is simplified away, which is why `simpa` appears in the derivation. The mathematical content is Mathlib's `sqrt x ^ 2 = x`, so this is a special case of `Real.sq_sqrt`. One caveat: the derivation is my own and could not be compiled here.

### [`EulerLpBochnerRealization.realization_ae`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/LpBochnerRealization.lean#L77-L81) — `lean-pool-0430`

Snippet: `samples/lean-pool/lean-pool-0430.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.MemLp.coeFn_toLp
- **file**: Mathlib/MeasureTheory/Function/LpSpace/Basic.lean
- **derivation**: (field_memLp w f hf hrep).coeFn_toLp
- **proof_uses_it**: True
- **explanation**: The library's `realization w f hf hrep` is defined as `(field_memLp w f hf hrep).toLp f`. Mathlib's `MemLp.coeFn_toLp` says that for `hf : MemLp f p μ`, `hf.toLp f =ᵐ[μ] f`. Once the definition is unfolded, the theorem is that lemma with the measure set to `μ.prod ν`, `p = 2`, and the `MemLp` proof set to `field_memLp w f hf hrep`. The current proof is exactly this one-line application. The substantive work (that `f` is in L²) is in the library's `field_memLp`, but the a.e.-equality statement itself is just `coeFn_toLp`.

### [`CKN.vlConv_apply_swap`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/Support/VorticityLocalizedEnergyWeakTime.lean#L78-L81) — `lean-pool-0443`

Snippet: `samples/lean-pool/lean-pool-0443.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: convolution_eq_swap
- **file**: Mathlib/Analysis/Convolution.lean
- **derivation**: by rw [vlConv, convolution_eq_swap]; simp [mul_comm]
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `convolution_eq_swap`, and the library's proof already uses that lemma. `vlConv k h` is defined in VorticityLocalizedEnergyKernel.lean as `convolution k h (ContinuousLinearMap.lsmul ℝ ℝ) volume`. `convolution_eq_swap` states `(f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ` for a general bilinear map `L` and measure `μ`. Taking `L = lsmul ℝ ℝ`, `μ = volume` and `G = Vec3` gives `∫ y, k (x - y) * h y`; `mul_comm` then turns this into the stated `∫ y, h y * k (x - y)`. The derivation is the library's own two-step proof. The more specific `convolution_lsmul_swap` (same file) would also work, again followed by `mul_comm`.

### [`AVenhance.FaaDiBruno.Product.harmonicOne_sq_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/FaaDiBruno/Product.lean#L293-L297) — `lean-pool-0462`

Snippet: `samples/lean-pool/lean-pool-0462.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sq_sum_le_card_mul_sum_sq
- **file**: Mathlib/Algebra/Order/Chebyshev.lean
- **derivation**: by simpa [Product.harmonicOne, Product.harmonicTwo, inv_pow] using
    sq_sum_le_card_mul_sum_sq (s := Finset.range m) (f := fun k : ℕ ↦ (k + 1 : ℝ)⁻¹)
- **explanation**: The library defines `harmonicOne m = ∑ k ∈ range m, (k+1)⁻¹` and `harmonicTwo m = ∑ k ∈ range m, ((k+1)^2)⁻¹`. Mathlib's `sq_sum_le_card_mul_sum_sq` states `(∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2`. Taking `s = range m` and `f k = (k+1 : ℝ)⁻¹` gives the theorem. The only glue needed is `card_range` and `inv_pow`, both handled by `simp`. The library's current proof uses the general Cauchy–Schwarz lemma `Finset.sum_mul_sq_le_sq_mul_sq` with the constant weight 1, not this lemma.

### [`CKN.Leray.integrable_mul_reflect`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegLocalEnergyBound.lean#L99-L101) — `lean-pool-0495`

Snippet: `samples/lean-pool/lean-pool-0495.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HasCompactSupport.convolutionExists_right
- **file**: Mathlib/Analysis/Convolution.lean
- **derivation**: hκc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) (hg.locallyIntegrable one_le_two) hκ x
- **explanation**: This is a special case of a Mathlib lemma. `HasCompactSupport.convolutionExists_right` says: if `g` has compact support and is continuous, and `f` is locally integrable, then `ConvolutionExists f g L μ` holds. By definition, `ConvolutionExistsAt f g x L μ` is `Integrable (fun t => L (f t) (g (x - t))) μ`.

Take `L := ContinuousLinearMap.mul ℝ ℝ`, use `κ` as the compactly supported continuous function and `g` as the locally integrable one, and evaluate at `x`. The result is `Integrable fun y => g y * κ (x - y)`, which matches the theorem up to unfolding `mul` (this should hold by `rfl`).

The local-integrability hypothesis comes from `MemLp.locallyIntegrable` with `1 ≤ 2`, which only changes the form of `hg`. The library's current proof does not use this lemma. It goes through its own `memLp_reflect` and `MemLp.integrable_mul`.

This is borderline. The derivation needs a second Mathlib lemma (`MemLp.locallyIntegrable`) to adjust a hypothesis. I count that as routine glue, but a stricter reading could treat it as combining two Mathlib results. I could not run Lean, so the derivation has not been compiled.

### [`Matrix.unitaryGroup.coe_hMul_star_self`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/InnerAut.lean#L139-L142) — `lean-pool-0499`

Snippet: `samples/lean-pool/lean-pool-0499.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Unitary.coe_mul_star_self
- **file**: Mathlib/Algebra/Star/Unitary.lean
- **derivation**: by simpa using Unitary.coe_mul_star_self a
- **explanation**: The library theorem is a duplicate of `Unitary.coe_mul_star_self`. In Mathlib, `Matrix.unitaryGroup n 𝕜` is an `abbrev` for `unitary (Matrix n n 𝕜)`. The Mathlib lemma `Unitary.coe_mul_star_self (U : unitary R) : (U : R) * star U = 1` needs only `[Monoid R] [StarMul R]`, and `Matrix n n 𝕜` over a field with `StarRing` meets these. So it applies with `R := Matrix n n 𝕜`, and its statement is the library's: the product of a unitary element and its star, as matrices, is 1. The two may differ only in where the coercion sits (`↑a * ↑(star a)` versus `↑(a * star a)`). Mathlib's `Unitary.mul_star_self`, together with the simp lemmas for the coercions, covers either form. That is why the derivation uses `simpa`. The library's current proof is a bare `simp_all`. It most likely closes the goal with Mathlib's simp lemmas `Unitary.mul_star_self` and `Unitary.mul_star_self_of_mem` rather than citing this lemma, so `proof_uses_it` is false.

### [`EuclideanSpace.orthonormalBasis.repr_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/ToMatrixOfEquiv.lean#L98-L101) — `lean-pool-0510`

Snippet: `samples/lean-pool/lean-pool-0510.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: EuclideanSpace.basisFun_repr
- **file**: Mathlib/Analysis/InnerProductSpace/PiL2.lean
- **derivation**: by ext x i; exact EuclideanSpace.basisFun_repr x i
- **explanation**: The library line `alias EuclideanSpace.orthonormalBasis := EuclideanSpace.basisFun` shows that `EuclideanSpace.orthonormalBasis` is just another name for Mathlib's `EuclideanSpace.basisFun`. So the theorem says `(EuclideanSpace.basisFun n 𝕜).repr = 1`, where `1` is the identity isometry. Mathlib defines `basisFun` as `⟨LinearIsometryEquiv.refl _ _⟩`. Mathlib's `EuclideanSpace.basisFun_repr` states the same fact pointwise: `(basisFun ι 𝕜).repr x i = x i`, also proved by `rfl`.

The two statements differ only in that one is pointwise and the other is an equality of maps. The `ext` lemmas `LinearIsometryEquiv.ext` and `PiLp.ext` turn one into the other, and `(1 : _) x` reduces to `x` by definition. The library's proof is `rfl` and does not cite the Mathlib lemma. I could not run Lean, so the one-line derivation has not been compiled.

I found no Mathlib lemma that states `repr = refl` or `repr = 1` for `basisFun` as a whole map.

Strictly, the allowed differences for a duplicate do not include switching between pointwise and whole-map forms, while the `special_case` rules do allow `ext`. So `special_case` could also be defended. I chose `duplicate` because no argument has to be specialised: the content is identical.

### [`NRR.Geometry.upperClosedHalfspace_convex`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/Geometry/ConvexBody/HalfspaceCut.lean#L91-L99) — `lean-pool-0523`

Snippet: `samples/lean-pool/lean-pool-0523.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: convex_halfSpace_ge
- **file**: Mathlib/Analysis/Convex/Basic.lean
- **derivation**: convex_halfSpace_ge ⟨inner_add_right u, fun c x => inner_smul_right u x c⟩ t
- **explanation**: Mathlib's `convex_halfSpace_ge (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 {w | r ≤ f w}`. The library defines `upperClosedHalfspace u t := {x | t ≤ inner ℝ u x}`, so the theorem is this lemma with f = (fun x => ⟪u, x⟫) and r = t. The `IsLinearMap` proof comes from `inner_add_right` and `inner_smul_right`; `(innerₛₗ ℝ u).isLinear` should also work. The replacement proof was not compiled. The library's current proof unfolds convexity by hand and finishes with linarith.

### [`TauCeti.DavisKahan.ExactSinTheta.sharp52_two_le_sqrt_ten`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean#L220-L222) — `lean-pool-0525`

Snippet: `samples/lean-pool/lean-pool-0525.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.le_sqrt_of_sq_le
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: Real.le_sqrt_of_sq_le (by norm_num)
- **explanation**: The theorem is a special case of `Real.le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y` with x = 2 and y = 10. The remaining side goal, `(2:ℝ)^2 ≤ 10`, is closed by `norm_num`. The library's current proof does not use this lemma: it calls `nlinarith` with `Real.sq_sqrt` and `Real.sqrt_nonneg`. `Real.le_sqrt'` with `.mpr` would also work.

### [`CK.mul'_π`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConnesKreimer/Core.lean#L1694-L1700) — `lean-pool-0540`

Snippet: `samples/lean-pool/lean-pool-0540.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgHom.comp_mul'
- **file**: Mathlib/Algebra/Algebra/Bilinear.lean
- **derivation**: (AlgHom.comp_mul' (π k)).symm
- **explanation**: This is a special case of `AlgHom.comp_mul'`. That lemma states that for any algebra hom `f : A →ₐ[R] B`, `f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap)`, where `μ` is notation for `LinearMap.mul'` and `⊗ₘ` for `TensorProduct.map`. Take `R := k`, `A := H k`, `B := Hab k` and `f := π k`; `π k` is defined in the library as an algebra hom `H k →ₐ[k] Hab k`. The result is the theorem with the two sides of the equation swapped, so `.symm` closes it. The verdict is special_case rather than duplicate because `f` has to be set to the library's own `π k`. The current proof does not cite this lemma. It runs `TensorProduct.ext'` and then `simp_all`, which is essentially how the Mathlib lemma itself is proved.

### [`Zeta32.Arith.Local.zmod_eq_iff_dvd`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta32/Arith/Local/PoleFun.lean#L41-L43) — `lean-pool-0553`

Snippet: `samples/lean-pool/lean-pool-0553.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: ZMod.intCast_eq_intCast_iff_dvd_sub
- **file**: Mathlib/Data/ZMod/Basic.lean
- **derivation**: eq_comm.trans (ZMod.intCast_eq_intCast_iff_dvd_sub b a p)
- **explanation**: The theorem is a duplicate, up to renaming the variables and swapping the sides of the equation. Mathlib's `ZMod.intCast_eq_intCast_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a` gives `(b : ZMod p) = a ↔ (p : ℤ) ∣ a - b` when applied to `b a p`. Putting `eq_comm` in front turns this into the library's statement `(a : ZMod p) = b ↔ (p : ℤ) ∣ a - b`. Neither version needs `p` to be prime; the library's lemma uses `omit hp` for this reason. The library's current proof goes another way: it rewrites with `ZMod.intCast_zmod_eq_zero_iff_dvd`, then uses `push_cast` and `sub_eq_zero`. If swapping the sides of the inner equation is not counted as a difference of presentation only, the verdict would be `special_case` instead, with the same one-line derivation.

### [`BollobasNikiforov.continuous_vecMulVec_self`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BollobasNikiforov/CP/Closed.lean#L51-L54) — `lean-pool-0578`

Snippet: `samples/lean-pool/lean-pool-0578.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Continuous.matrix_vecMulVec
- **file**: Mathlib/Topology/Instances/Matrix.lean
- **derivation**: continuous_id.matrix_vecMulVec continuous_id
- **proof_uses_it**: True
- **explanation**: This is a special case of `Continuous.matrix_vecMulVec`. That lemma says: if `A` and `B` are continuous, then `fun x => vecMulVec (A x) (B x)` is continuous, for any `R` with `[Mul R] [ContinuousMul R]`. The library's lemma takes `R = ℝ`, `X = n → ℝ` and `A = B = id`. The current proof is already exactly this one-line application.

### [`Real.exists_eq_of_iSup_eq_of_finite_domain`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/WhiteheadTheorem/Auxiliary.lean#L96-L110) — `lean-pool-0599`

Snippet: `samples/lean-pool/lean-pool-0599.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: exists_eq_ciSup_of_finite
- **file**: Mathlib/Order/ConditionallyCompleteLattice/Finset.lean
- **derivation**: by have := hfz.nonempty; subst hf; exact exists_eq_ciSup_of_finite
- **explanation**: Mathlib's `exists_eq_ciSup_of_finite [ConditionallyCompleteLinearOrder α] [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨆ i, f i` is the general version. This theorem is the case α := ℝ. Its hypothesis `hfz` is only needed to get `Nonempty ι`, and `hf` just gives the supremum the name `a`, so `subst hf` removes it. The library's proof argues by contradiction using `lt_ciSup_iff` and `Set.Finite.ciSup_lt_iff`; it does not use this lemma.

### [`EllipticPdes.Extension.stepProfile_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EllipticPDE/Extension/Cutoff.lean#L57-L58) — `lean-pool-0610`

Snippet: `samples/lean-pool/lean-pool-0610.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.smoothTransition.one_of_one_le
- **file**: Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean
- **derivation**: Real.smoothTransition.one_of_one_le (by linarith)
- **proof_uses_it**: True
- **explanation**: The library defines `stepProfile t := Real.smoothTransition (t - 1)`, so it is `smoothTransition` shifted by 1. Mathlib's `Real.smoothTransition.one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1` gives the theorem directly once `x` is set to `t - 1`. The side condition `1 ≤ t - 1` follows from `2 ≤ t` by `linarith`. The library's proof is already exactly this one-line application. The mathematical content (smoothTransition equals 1 from 1 onward) is Mathlib's; the library definition only shifts the argument.

### [`CKN.Core.Step4.min_kappa_pos`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/Step4/KappaCapArithmetic.lean#L57-L62) — `lean-pool-0622`

Snippet: `samples/lean-pool/lean-pool-0622.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: lt_min
- **file**: Mathlib/Order/Defs/LinearOrder.lean
- **derivation**: lt_min (by positivity) hq
- **proof_uses_it**: True
- **explanation**: The theorem is Mathlib's `lt_min : a < b → a < c → a < min b c` with `a := 0`, `b := (1 / τ + 8 / 25)⁻¹` and `c := q`, specialised to ℝ. Its first hypothesis, `0 < (1 / τ + 8 / 25)⁻¹`, is a side goal that `positivity` closes from `hτ`. The library's proof already ends with `lt_min hkappa hq`; it just proves `hkappa` with `inv_pos` instead of a single `positivity` call. The result carries no content of its own beyond `lt_min` plus a routine positivity check.

### [`TauCeti.DavisKahan.Section4.sourceRestrictedDisplacement_extendDomainByZero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Geometry/Polar/RestrictedDisplacementExtremal.lean#L986-L993) — `lean-pool-0646`

Snippet: `samples/lean-pool/lean-pool-0646.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.adjoint_subtypeL
- **file**: Mathlib/Analysis/InnerProductSpace/Adjoint.lean
- **derivation**: by rw [sourceRestrictedDisplacement, ContinuousLinearMap.comp_assoc, Submodule.adjoint_subtypeL]; rfl
- **proof_uses_it**: True
- **explanation**: This is a borderline call. The library defines `sourceRestrictedDisplacement U T := (1 - T) ∘L U.subtypeL`, so the theorem says `(1 - T) ∘L U.subtypeL ∘L U.subtypeL† = (1 - T) ∘L U.starProjection`. Mathlib's `Submodule.adjoint_subtypeL` states `U.subtypeL† = U.orthogonalProjectionOnto`. Mathlib also defines `U.starProjection` as `U.subtypeL ∘L U.orthogonalProjectionOnto`, so the right-hand side matches by unfolding (`rfl`). The derivation therefore takes three steps: unfold the library definition, reassociate the composition, and rewrite with `adjoint_subtypeL`. The only real mathematical content is that the adjoint of the subspace inclusion is the orthogonal projection, and that is exactly the Mathlib lemma. The current proof already uses it: `ext x; simp [sourceRestrictedDisplacement, Submodule.adjoint_subtypeL]`. I have not compiled the suggested derivation. It may need `simp` instead of `rfl` if the instance arguments do not line up definitionally.

### [`Bananas.int_eq_of_emod_sub_eq_zero_of_fundamental`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BrillNoetherGraphs/Bananas/Transmission/ExactTorsionAPI.lean#L201-L220) — `lean-pool-0648`

Snippet: `samples/lean-pool/lean-pool-0648.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Int.eq_zero_of_abs_lt_dvd
- **file**: Mathlib/Algebra/Order/Group/Unbundled/Int.lean
- **derivation**: sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero hmod) (abs_lt.mpr ⟨by omega, by omega⟩))
- **explanation**: Int.eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0. Set m = k and x = b - c. The divisibility comes from hmod via Int.dvd_of_emod_eq_zero. The bound |b - c| < k follows from the range hypotheses by abs_lt and omega. sub_eq_zero.mp then turns b - c = 0 into b = c. The library's proof uses the Lean core lemma Int.eq_zero_of_dvd_of_natAbs_lt_natAbs and needs extra natAbs/|·| conversions. Other routes found: Nat.ModEq.eq_of_lt_of_lt is the same fact for ℕ only, and Int.emod_eq_emod_iff_emod_sub_eq_zero plus Int.emod_eq_of_lt works but needs two lemmas. The derivation was not compiled.

### [`BGS.Markoff.weightedSplitTraceLaurent_smooth_of_partialLocalizations`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/Markoff/TraceCurve/LaurentSmooth.lean#L385-L424) — `lean-pool-0653`

Snippet: `samples/lean-pool/lean-pool-0653.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RingHom.Smooth.ofLocalizationSpanTarget
- **file**: Mathlib/RingTheory/RingHom/Smooth.lean
- **derivation**: RingHom.smooth_algebraMap.mp (RingHom.Smooth.ofLocalizationSpanTarget _ _ hspan (by
  rintro ⟨r, rfl | rfl⟩ <;> rw [← IsScalarTower.algebraMap_eq, RingHom.smooth_algebraMap] <;> assumption))
- **explanation**: `RingHom.Smooth.ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth` says: for f : R →+* S and s : Set S with Ideal.span s = ⊤, if (algebraMap S (Localization.Away r)).comp f is smooth for every r ∈ s, then f is smooth. Instantiating R = K, S = L, f = algebraMap K L and s = {fx, fy} gives the library theorem; hspan is exactly the spanning hypothesis. Only routine glue is needed: `RingHom.smooth_algebraMap` converts between RingHom.Smooth and Algebra.Smooth, and `IsScalarTower.algebraMap_eq` identifies the composite K → L → L_f with algebraMap K L_f, so hX and hY supply the local hypotheses. The lemma needs R and S in the same universe, which holds because L is a Localization.Away of a ring built over K. The derivation was not compiled. The library proof does not call this lemma: it repeats Mathlib's own proof of it by hand, via `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.smoothLocus_eq_univ_iff`. It is not a duplicate because Mathlib states the result for ring homomorphisms and an arbitrary spanning set, while the library states the Algebra.Smooth version for a specific two-element set.

### [`Subtype.val_comp_single`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BruhatTits/Utils/Subring.lean#L24-L28) — `lean-pool-0654`

Snippet: `samples/lean-pool/lean-pool-0654.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.single_op
- **file**: Mathlib/Algebra/Notation/Pi/Basic.lean
- **derivation**: (Pi.single_op (fun _ => (Subtype.val : A → R)) (fun _ => ZeroMemClass.coe_zero A) i a).symm
- **explanation**: This is a special case of `Pi.single_op`, but I couldn't compile the derivation, so it is unchecked. `Pi.single_op` is the additive version of `Pi.mulSingle_op`. It states `Pi.single i (op i x) = fun j => op j (Pi.single i x j)` for any family of maps `op` that send 0 to 0.

Take `op := fun _ => Subtype.val`. The side condition `((0 : A) : R) = 0` is `ZeroMemClass.coe_zero`, which should also be closable by `rfl` or `simp`. The right-hand side `fun j => ↑(Pi.single i a j)` is definitionally equal to `Subtype.val ∘ Pi.single i a`, so `.symm` gives the theorem.

`Pi.apply_single` gives the same fact pointwise (the library proof's `ext j` plus a case split is exactly that). The library's current proof uses `ext j` and `by_cases ... <;> aesop` rather than this lemma.

Mathlib has a closely analogous lemma, `RestrictedProduct.comp_single`, about the coercion out of a restricted product, but it does not apply to subrings. I found no Mathlib lemma stating `Subtype.val ∘ Pi.single` directly.

### [`BGS.HasseWeil.isGalois_exactConstantExtension_over_frobeniusTwistField`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/HasseWeil/ExactConstantExtensionFrobeniusTwist.lean#L291-L310) — `lean-pool-0661`

Snippet: `samples/lean-pool/lean-pool-0661.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsGalois.of_fixed_field
- **file**: Mathlib/FieldTheory/Galois/Basic.lean
- **derivation**: letI := exactConstantExtensionField C N S hExact; letI := exactConstantExtensionBaseAlgebra C L N S; haveI := finiteDimensional_exactConstantExtension_over_base C L N S hExact
exact IsGalois.of_fixed_field (ExactConstantExtension C N S) (exactConstantExtensionFrobeniusTwistSubgroup C L N S g)
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's instance `IsGalois.of_fixed_field (E) (G) [Group G] [Finite G] [MulSemiringAction G E] : IsGalois (FixedPoints.subfield G E) E`, which says that if a finite group acts on a field E, then E is Galois over the fixed field.

In the library, `exactConstantExtensionFrobeniusTwistField` is defined as `IntermediateField.fixedField H`, where H is the subgroup of `ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S` generated by the Frobenius twist (`Subgroup.zpowers`). The derivation takes E := ExactConstantExtension C N S and G := H. `IntermediateField.fixedField H` is definitionally `FixedPoints.subfield H E` as an extension, so after unfolding the definition the goal is exactly the Mathlib instance.

The library proof does the same thing: it unfolds with `change` and then applies `IsGalois.of_fixed_field`. The one non-routine part is the `Finite H` instance, which needs E to be finite-dimensional over L. The library gets this from its own lemma `finiteDimensional_exactConstantExtension_over_base`, which makes this a borderline case for the "routine glue" rule. Mathlib supplies all of the Galois-theoretic content.

### [`RS.Cech.H1.induction_on`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/Cech/Colimit.lean#L112-L115) — `lean-pool-0668`

Snippet: `samples/lean-pool/lean-pool-0668.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.DirectLimit.induction_on
- **file**: Mathlib/Algebra/Colimit/Module.lean
- **derivation**: Module.DirectLimit.induction_on ξ ih
- **proof_uses_it**: True
- **explanation**: This is a special case of `Module.DirectLimit.induction_on`. In the library, `H1 D` is an `abbrev` for `Module.DirectLimit (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D h)`, indexed by `FinCover ⊤`. `toH1 D 𝒰` is defined as `Module.DirectLimit.of ℂ _ _ _ 𝒰`. Mathlib's lemma says: in a direct limit over a nonempty directed index type, a predicate C holds for every element z if it holds for every `of R ι G f i x`. The theorem takes that lemma with this particular direct system and with ι := FinCover ⊤. It adds no mathematical content of its own, and the library's proof is exactly a one-line application of the Mathlib lemma.

### [`lmul_eq_zero_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/LmulRmul.lean#L152-L154) — `lean-pool-0683`

Snippet: `samples/lean-pool/lean-pool-0683.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: LinearMap.mulLeft_eq_zero_iff
- **file**: Mathlib/Algebra/Module/LinearMap/Basic.lean
- **derivation**: LinearMap.mulLeft_eq_zero_iff _ _ _
- **proof_uses_it**: True
- **explanation**: The library defines `lmul x` with `toFun x := LinearMap.mulLeft R x`, and `lmul_eq_mul : lmul x = LinearMap.mulLeft R x` holds by `rfl`. So `lmul x = 0 ↔ x = 0` is exactly Mathlib's `LinearMap.mulLeft_eq_zero_iff : mulLeft R a = 0 ↔ a = 0`, once that wrapper is unfolded. Mathlib's lemma assumes less: a non-unital, non-associative semiring with a module structure and `SMulCommClass R A A`. Those assumptions hold for the theorem's `[Semiring H₁] [Algebra R H₁]`, so the lemma applies directly with no instantiation. The library's current proof is simply that Mathlib lemma. `lmul` is a thin wrapper around Mathlib's `mulLeft`, not new content of the library, so I count this as a duplicate.

### [`dist_le_integral_of_norm_deriv_le_of_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SardMoreira/ToMathlib/PR32186.lean#L28-L60) — `lean-pool-0702`

Snippet: `samples/lean-pool/lean-pool-0702.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: norm_sub_le_integral_of_norm_deriv_le_of_le
- **file**: Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean
- **derivation**: by rw [dist_eq_norm_sub']; exact norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd hfB hBi
- **explanation**: Mathlib's `norm_sub_le_integral_of_norm_deriv_le_of_le` has exactly the same hypotheses: `a ≤ b`, `f` continuous on `Icc a b` and differentiable on `Ioo a b`, `‖deriv f t‖ ≤ B t` for a.e. `t` in `Ioo a b`, and `B` interval-integrable on `a..b`. Its conclusion is `‖f b - f a‖ ≤ ∫ t in a..b, B t`. The library states the left side as `dist (f a) (f b)`, which equals `‖f b - f a‖` in a normed group by `dist_eq_norm_sub'`; this is only a difference in surface form. The library proof does not call the Mathlib lemma: it copies Mathlib's proof almost line for line (completion reduction, then `integral_eq_sub_of_hasDeriv_right` and `norm_integral_le_of_norm_le`). The file name `ToMathlib/PR32186.lean` suggests the lemma was later upstreamed under the `norm_sub_` name.

### [`TriangleInflation.Graph.Sound.empty_fun_eq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Graph/Soundness.lean#L580-L581) — `lean-pool-0711`

Snippet: `samples/lean-pool/lean-pool-0711.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.uniqueOfIsEmpty
- **file**: Mathlib/Basic/Unique.lean
- **derivation**: Subsingleton.elim f g
- **explanation**: The theorem says that any two functions out of the empty finset's subtype are equal. Mathlib already has this through an instance. `Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) : Unique (∀ a, β a)` (Mathlib/Basic/Unique.lean) gives a `Unique` instance on functions from an empty type. Mathlib/Data/Finset/Empty.lean provides `Finset.instIsEmpty : IsEmpty (∅ : Finset α)`. Taking α := ↥(∅ : Finset (GObs Γ t)) and β := fun _ => Bool gives `Unique (↥∅ → Bool)`, so the function type is a subsingleton and `Subsingleton.elim f g` proves the statement (I did not compile this). The library proves it by hand with `funext` and `Finset.notMem_empty` instead. I searched for a plain-function lemma such as `eq_of_isEmpty` or `funext_isEmpty` and found only versions for bundled continuous maps (`BoundedContinuousFunction.eq_of_empty` and similar), not one for ordinary functions. The match is through an instance rather than a named lemma, and the result is close to a generic logical fact, so the `special_case` verdict is borderline.

### [`Chudnovsky.modularForm_SL_smul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Chudnovsky/SingularModuli/JFunction.lean#L80-L89) — `lean-pool-0725`

Snippet: `samples/lean-pool/lean-pool-0725.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SlashInvariantForm.slash_action_eqn''
- **file**: Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean
- **derivation**: SlashInvariantForm.slash_action_eqn'' f ⟨γ, rfl⟩ τ
- **explanation**: Mathlib's `slash_action_eqn''` says: for any `Γ : Subgroup (GL (Fin 2) ℝ)` with `[Γ.HasDetOne]`, any `f` in a `SlashInvariantFormClass F Γ k`, and any `γ ∈ Γ`, we have `f (γ • z) = denom γ z ^ k * f z`. Instantiate `Γ := 𝒮ℒ = (mapGL ℝ : SL(2,ℤ) →* GL).range`. The `HasDetOne` instance for `(mapGL S).range` exists in `ArithmeticSubgroups.lean`, and the membership proof is `⟨γ, rfl⟩`. The `SL(2,ℤ)` action on `ℍ` and `denom` both go through the `mapGL ℝ` image, so the statement should match up to definitional unfolding (not checked in Lean). The theorem fixes the subgroup to `𝒮ℒ`, so it is a special case. The library's proof unfolds the slash action by hand (`SL_slash_apply`, `div_eq_iff`) instead of using this lemma.

### [`BGS.Markoff.splitTraceLaurentToKummerTop_algebraMap_apply`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/Markoff/TraceCurve/Localization.lean#L329-L349) — `lean-pool-0734`

Snippet: `samples/lean-pool/lean-pool-0734.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsLocalization.Away.lift_eq
- **file**: Mathlib/RingTheory/Localization/Away/Basic.lean
- **derivation**: simp only [splitTraceLaurentToKummerTop, IsLocalization.Away.liftAlgHom_apply]
apply IsLocalization.Away.lift_eq
- **proof_uses_it**: True
- **explanation**: The library defines `splitTraceLaurentToKummerTop` as `IsLocalization.Away.liftAlgHom` of `splitTraceAffineToKummerTop`, taken from the Laurent ring, which is the localization of the affine coordinate ring away from some element. The theorem says this lift sends `algebraMap a` to `splitTraceAffineToKummerTop a`. That is exactly Mathlib's `IsLocalization.Away.lift_eq : lift x hg (algebraMap R S a) = g a`, applied to the library's specific rings and map. The only step needed is unfolding the definition and rewriting with `liftAlgHom_apply`, which holds by `rfl`. The current proof already does this. So the result is an instance of `lift_eq` once the library's definition is unfolded. Its only content beyond that lemma is the library's own definition, which makes this a borderline case.

### [`AVenhance.Infra.Section5.Contracts.sd_spaceGrad_add`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredSplitCalculus.lean#L27-L32) — `lean-pool-0736`

Snippet: `samples/lean-pool/lean-pool-0736.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: fderiv_fun_add
- **file**: Mathlib/Analysis/Calculus/FDeriv/Add.lean
- **derivation**: congrArg (fun L => L (basisVec i)) (fderiv_fun_add hf hg)
- **proof_uses_it**: True
- **explanation**: The library defines `spaceGrad f x i` as `fderiv ℝ f x (basisVec i)` in `AVenhance/Statements/Roots/SpaceGrad.lean`. Once that definition is unfolded, the theorem is Mathlib's `fderiv_fun_add` (`fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x`, assuming `DifferentiableAt` for `f` and `g`), applied to the vector `basisVec i` and specialised to `Vec 2 → ℝ`. The library's proof already does exactly this: it unfolds `spaceGrad`, rewrites with `fderiv_fun_add hf hg`, and closes with `rfl`. Mathlib supplies all of the mathematical content, the derivative of a sum. The library only adds the wrapper that evaluates the derivative at a basis vector. The one-line `congrArg` derivation should check by definitional unfolding of `spaceGrad`, but I could not run Lean to confirm it. If it fails, the current three-step proof works as it stands.

### [`UnrestrictedBooleanMul.N4.f2_mul_self_quartic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanMultiplication/N4/QuarticLowLow.lean#L30-L31) — `lean-pool-0767`

Snippet: `samples/lean-pool/lean-pool-0767.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ZMod.pow_card
- **file**: Mathlib/FieldTheory/Finite/Basic.lean
- **derivation**: by simpa [sq] using ZMod.pow_card (p := 2) u
- **explanation**: The library defines `F₂` as `abbrev F₂ := ZMod 2`. Mathlib's `ZMod.pow_card (x : ZMod p) [Fact p.Prime] : x ^ p = x` with `p := 2` gives `u ^ 2 = u`; the instance `Nat.fact_prime_two` supplies primality. Rewriting `u ^ 2` as `u * u` with `sq` gives the theorem. The current proof doesn't use this lemma: it splits into the cases u = 0 and u = 1 and closes each with `simp`. I found no closer match: Mathlib has no `BooleanRing (ZMod 2)` instance and no lemma stating `a * a = a` for `ZMod 2`.

### [`FelsConjectureProof.binomial_sum_eq_add_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/FelConjecture/Solution.lean#L1950-L1955) — `lean-pool-0770`

Snippet: `samples/lean-pool/lean-pool-0770.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: add_pow
- **file**: Mathlib/Data/Nat/Choose/Sum.lean
- **derivation**: by rw [add_pow]; exact Finset.sum_congr rfl fun k _ => by ring
- **proof_uses_it**: True
- **explanation**: This is the binomial theorem for ℚ, so it is a special case of Mathlib's `add_pow`. Mathlib states `add_pow [CommSemiring R] (x y : R) (n : ℕ) : (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m`. The library theorem takes R := ℚ, swaps the two sides of the equation, and writes each term as `choose * a^k * b^(n-k)` instead of `a^k * b^(n-k) * choose`. Because of that reordering, a short `sum_congr`/`ring` step is needed after rewriting with `add_pow`. The library's current proof already does exactly this. I searched for a variant of `add_pow` with the binomial coefficient written first and did not find one: `add_pow'` sums over the antidiagonal with `•` instead.

### [`Mathoverflow1973.Smale.PartialChart.bijective_mfderiv`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/HopfProblem/Recognition/Smale2.lean#L2224-L2233) — `lean-pool-0775`

Snippet: `samples/lean-pool/lean-pool-0775.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective
- **file**: Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean
- **derivation**: (⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩ :
  Φ.toOpenPartialHomeomorph.MDifferentiable I J).mfderiv_bijective hx
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective` says: if `e` is an open partial homeomorphism that is differentiable in both directions (`he : e.MDifferentiable I I'`), then `mfderiv I I' e x` is bijective for every `x ∈ e.source`. The library theorem takes `e := Φ.toOpenPartialHomeomorph`. That is the partial homeomorphism underlying the C^∞ `PartialDiffeomorph` Φ, and `toFun'_toOpenPartialHomeomorph` says it coerces to `⇑Φ` by `rfl`.

The hypothesis `he` comes from Mathlib's own `PartialDiffeomorph.mdifferentiableOn`, applied to Φ and to `Φ.symm`. The side condition `∞ ≠ 0` is closed by `simp`. The library's proof already does exactly this, in two lines.

I looked for a lemma stated directly for `PartialDiffeomorph` and found none. Mathlib only has `isInvertible_mfderiv` lemmas, for `Diffeomorph`, `IsLocalDiffeomorphAt` and `IsLocalDiffeomorph`. They give `IsInvertible` rather than `Bijective`, so they don't give a shorter derivation.

### [`pentagonal_injective''`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PentagonalNumberTheorem/Old.lean#L68-L73) — `lean-pool-0779`

Snippet: `samples/lean-pool/lean-pool-0779.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: pentagonal_injective
- **file**: Mathlib/Combinatorics/Enumerative/Pentagonal/Basic.lean
- **derivation**: fun a b h => pentagonal_injective (by rw [pentagonal_def, pentagonal_def]; exact congrArg Int.toNat h)
- **explanation**: The closest match is Mathlib's `pentagonal_injective : Function.Injective pentagonal`, where `pentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat`. The library's `pentagonal''` uses the same formula `k * (3 * k - 1) / 2`, but returns an `ℤ` instead of taking `.toNat`. This is not a different setting, so the statement is not literally the same as Mathlib's. Still, the injectivity content is identical. From `h : pentagonal'' a = pentagonal'' b`, applying `Int.toNat` to both sides gives `pentagonal a = pentagonal b`, once `pentagonal` is unfolded with `pentagonal_def` (its body is not exposed under the module system). Mathlib's lemma then gives `a = b`. That is routine glue around one Mathlib lemma: unfolding definitions plus `congrArg`. The library proves it instead through its own `two_pentagonal''` and `two_pentagonal_inj''`.

### [`TriangleInflation.Graph.swapTwist_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Graph/DoubleStar.lean#L317-L318) — `lean-pool-0781`

Snippet: `samples/lean-pool/lean-pool-0781.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.swap_apply_left
- **file**: Mathlib/Logic/Equiv/Basic.lean
- **derivation**: Equiv.swap_apply_left 0 (j e)
- **proof_uses_it**: True
- **explanation**: This is a special case of `Equiv.swap_apply_left (a b : α) : swap a b a = b`. In the library, `swapTwist j e` is defined as `Equiv.swap 0 (j e)`, so it is only a wrapper. Once that definition is unfolded, the theorem is Mathlib's lemma with `α := Fin 2`, `a := 0` and `b := j e`. The library's proof already applies this lemma directly, as a single term.

### [`Polynomial.shiftedLegendre_poly_eval_zero_eq_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta3Irrational/LegendrePoly.lean#L342-L359) — `lean-pool-0784`

Snippet: `samples/lean-pool/lean-pool-0784.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
- **file**: Mathlib/Algebra/Polynomial/Derivative.lean
- **derivation**: obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd m (dvd_mul_right (X ^ n : ℝ[X]) ((1 - X) ^ n))
rw [hq]; simp [Nat.sub_ne_zero_of_lt h]
- **explanation**: This is a borderline call. I'm calling it a special case of `Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd`, which says that `q ^ n ∣ p` implies `q ^ (n - m) ∣ derivative^[m] p`. That lemma does the real work. Here we take `q = X` and `p = X ^ n * (1 - X) ^ n`, where `X ^ n ∣ p` holds by `dvd_mul_right`. This gives `X ^ (n - m) ∣ derivative^[m] p`. Since `m < n`, the exponent `n - m` is nonzero, so evaluating at 0 gives `0 ^ (n - m) * eval 0 q' = 0`.

The step from divisibility to "evaluates to 0 at 0" is the only glue: unpack the divisibility, rewrite, then `simp` with `eval_mul`, `eval_pow`, `eval_X` and `zero_pow`. I could not run Lean, so this two-line derivation is untested.

The library proves the result another way: it expands the product with the Leibniz rule (`iterate_derivative_mul`) and shows each term is zero.

A related lemma is `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity` in `Mathlib/Algebra/Polynomial/FieldDivision.lean`. Using it would also require proving that the root multiplicity at 0 is at least `n`, so the divisibility lemma gives the shorter route.

### [`ESS.spatialDeriv_eq_zero_of_notMem_tsupport`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Endpoint/LocalDivCurlCutoff.lean#L46-L49) — `lean-pool-0802`

Snippet: `samples/lean-pool/lean-pool-0802.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: fderiv_of_notMem_tsupport
- **file**: Mathlib/Analysis/Calculus/FDeriv/Const.lean
- **derivation**: by simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hx]
- **explanation**: This is a special case of Mathlib's `fderiv_of_notMem_tsupport`. In the library, `spatialDeriv g i x` is defined as `(fderiv ℝ g x) (basisVec i)`. Mathlib's `fderiv_of_notMem_tsupport (𝕜) (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0` says the whole derivative is zero at any point outside `tsupport f`. Taking `𝕜 = ℝ` makes `fderiv ℝ g x = 0`. Applying that zero map to `basisVec i` gives 0, and unfolding `spatialDeriv` plus `simp` handles this step. The library's current proof uses different Mathlib lemmas, `image_eq_zero_of_notMem_tsupport` together with `tsupport_fderiv_apply_subset`, so it does not apply `fderiv_of_notMem_tsupport`.

### [`Model.Field.ringChar_eq_of_Prime`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EcTateLean/Algebra/EllipticCurve/Model.lean#L508-L517) — `lean-pool-0813`

Snippet: `samples/lean-pool/lean-pool-0813.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CharP.ringChar_of_prime_eq_zero
- **file**: Mathlib/Algebra/CharP/Basic.lean
- **derivation**: CharP.ringChar_of_prime_eq_zero hnp (by rwa [Nat.cast_ofNat])
- **explanation**: This duplicates `CharP.ringChar_of_prime_eq_zero`. The Mathlib lemma states `[NonAssocSemiring R] [Nontrivial R] (hprime : p.Prime) (hp0 : (p : R) = 0) : ringChar R = p`. Its hypotheses are weaker than the library's: it needs only a nontrivial non-associative semiring, where the theorem assumes a field, and it does not need `Nat.AtLeastTwo n`. The only other difference is surface form. The library writes the numeral `OfNat.ofNat n`, while Mathlib uses the cast `(n : K)`. For `n` with `AtLeastTwo`, these two are identified by `Nat.cast_ofNat`. The library's proof does the same thing as Mathlib's: it uses `ringChar.spec` to get that `ringChar K` divides the prime `n`, then rules out characteristic 1. It does not call the Mathlib lemma.

### [`CompactSelfAdjoint.exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CompactSpectral/Analysis/InnerProductSpace/RayleighCompact.lean#L296-L332) — `lean-pool-0854`

Snippet: `samples/lean-pool/lean-pool-0854.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.IsSymmetric.inner_map_self_eq_zero
- **file**: Mathlib/Analysis/InnerProductSpace/Symmetric.lean
- **derivation**: by_contra! h; refine h0 (ContinuousLinearMap.coe_injective ?_)
simpa using hT.isSymmetric.inner_map_self_eq_zero.mp fun x => by rw [← hT.isSymmetric.coe_reApplyInnerSelf_apply, h x, RCLike.ofReal_zero]
- **explanation**: The Mathlib lemma `LinearMap.IsSymmetric.inner_map_self_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (∀ x, ⟪T x, x⟫ = 0) ↔ T = 0` says that a symmetric operator with zero quadratic form is zero. The library theorem is its contrapositive, applied to the coercion of a self-adjoint continuous linear map. The library writes the quadratic form as `reApplyInnerSelf`, the real part of ⟪T x, x⟫. For a symmetric operator, the rewrite lemma `IsSymmetric.coe_reApplyInnerSelf_apply` (in the same file) turns `reApplyInnerSelf` back into ⟪T x, x⟫. `ContinuousLinearMap.coe_injective` then lifts `↑T = 0` to `T = 0`. The library's proof does not use the lemma: it redoes the polarization argument by hand with `inner_map_polarization`. The case is borderline: the derivation needs one extra rewrite lemma besides the main one, but that lemma only converts the real part of the inner product into the inner product itself. I also looked at `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` in Rayleigh.lean as another route, but deriving the result from it takes more steps.

### [`HahnSeries.exists_max_mem_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/HahnSeries/EPrimitive.lean#L99-L109) — `lean-pool-0877`

Snippet: `samples/lean-pool/lean-pool-0877.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.exists_max_image
- **file**: Mathlib/Data/Set/Finite/Lemmas.lean
- **derivation**: Set.exists_max_image _ id hfin (HahnSeries.support_nonempty_iff.mpr hx)
- **explanation**: The file states `Set.exists_min_image` and tags it `@[to_dual]`, which generates `Set.exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) : s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a`. Setting s := x.support and f := id gives the theorem. Finiteness is `hfin`; non-emptiness comes from Mathlib's `HahnSeries.support_nonempty_iff.mpr hx`. The conclusion `id g ≤ id a` is definitionally `g ≤ a`. The current proof does the same thing through `Finset.exists_max_image` with `id` on `hfin.toFinset`, not the Set version.

### [`ESS.blowupLimitClauses_restrict_prod_eq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Endpoint/BlowupLimitClausesModulusEstimate.lean#L34-L40) — `lean-pool-0878`

Snippet: `samples/lean-pool/lean-pool-0878.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.prod_restrict
- **file**: Mathlib/MeasureTheory/Measure/Prod.lean
- **derivation**: by rw [Measure.prod_restrict]; rfl
- **proof_uses_it**: True
- **explanation**: The Mathlib lemma `Measure.prod_restrict` says `(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`. In the library, `ParabolicPoint` is defined as `Vec3 × ℝ` and `spaceTimeSet C I` as `C ×ˢ I`. Its volume on `ParabolicPoint` is definitionally `volume.prod volume`, which is why the `rfl` in the current proof closes the goal. So the theorem is the lemma with μ = ν = volume, s = C and t = I, with the sides swapped and the library's definitions unfolded. The current proof already uses it: `rw [Measure.prod_restrict]; rfl`.

### [`CarlsonFunctions.SeveralComplexVariables.torusMap_mem_closedPolydisc`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/Polydisc.lean#L145-L149) — `lean-pool-0885`

Snippet: `samples/lean-pool/lean-pool-0885.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: circleMap_mem_closedBall
- **file**: Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean
- **derivation**: fun i _ => circleMap_mem_closedBall (c i) hR (θ i)
- **explanation**: `closedPolydisc c R` is the library's own definition, `Set.pi univ fun i => closedBall (c i) R`. By definition, `torusMap c (fun _ => R) θ i = c i + R * exp (θ i * I)`, and this is definitionally equal to `circleMap (c i) R (θ i)`. So membership in the closed polydisc means: for each coordinate `i`, `circleMap (c i) R (θ i) ∈ closedBall (c i) R`. That is exactly Mathlib's `circleMap_mem_closedBall (c : ℂ) (hR : 0 ≤ R) (θ : ℝ)`, applied once per coordinate. The only glue is unfolding `Set.pi`. I did not compile the derivation; it relies on the two maps being definitionally equal, which holds by unfolding. Mathlib's `TorusIntegral.lean` has no lemma placing `torusMap` in a product of closed balls; its `torusMap` lemmas are `torusMap_sub_center`, `torusMap_eq_center_iff` and `torusMap_zero_radius`. The library's proof gets the result with `simp` instead.

### [`measure_ball_pos_of_mem_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/FormalizingGMT/TangentMeasures/Basic.lean#L193-L196) — `lean-pool-0898`

Snippet: `samples/lean-pool/lean-pool-0898.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.mem_support_iff_forall
- **file**: Mathlib/MeasureTheory/Measure/Support.lean
- **derivation**: (Measure.mem_support_iff_forall a).mp ha _ (ball_mem_nhds a hρ)
- **proof_uses_it**: True
- **explanation**: `Measure.mem_support_iff_forall` says `x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U`, for any topological measurable space. The library's lemma takes `U` to be `ball a ρ`. The only extra step is the side condition that this ball is a neighbourhood of `a`, which `ball_mem_nhds a hρ` supplies. That step is trivial and could arguably be done another way too: `(Metric.nhds_basis_ball.mem_measureSupport).mp ha ρ hρ`, using `Filter.HasBasis.mem_measureSupport`. The library's current proof is exactly this one-line application. Mathlib has no version of the lemma stated with balls: I read all of `Measure/Support.lean` and grepped for `support` together with `ball`.

### [`NavierStokes.FlatCovariance.determinant_columns`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TorusAverages.lean#L736-L739) — `lean-pool-0901`

Snippet: `samples/lean-pool/lean-pool-0901.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.det_mul_row
- **file**: Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean
- **derivation**: by simpa [columns, Fin.prod_univ_two] using Matrix.det_mul_row c G
- **explanation**: The library defines `columns G c := fun i j => c j * G i j`. Mathlib's `Matrix.det_mul_row (v : n → R) (A : Matrix n n R)` states `det (of fun i j => v j * A i j) = (∏ i, v i) * det A`, which is exactly the same matrix. Taking `n = Fin 2`, `v = c` and `A = G`, and expanding the product with `Fin.prod_univ_two` to get `c 0 * c 1`, gives the theorem. The library's current proof instead expands the determinant with `det_fin_two` and finishes with `ring`.

### [`LeanPool.DemazureProduct.Valley.min_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DemazureProduct/Valley.lean#L68-L70) — `lean-pool-0918`

Snippet: `samples/lean-pool/lean-pool-0918.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.min'_mem
- **file**: Mathlib/Order/Finset/Max.lean
- **derivation**: by simpa [min, Finset.mem_image] using Finset.min'_mem (Finset.image v.f (v.floor (v.f 0))) (v.floor_image_nonempty 0)
- **proof_uses_it**: True
- **explanation**: This is a borderline case. `Valley.min` is defined directly as `Finset.min'` of the finite set `Finset.image v.f (v.floor (v.f 0))`. `Finset.min'_mem` says that `s.min' H ∈ s`. Applying it to this set and unfolding `min`, `Finset.mem_image` and `mem_floor` by `simp` gives exactly `∃ a ∈ {n | v.f n ≤ v.f 0}, v.f a = v.min`. That is the library's current one-line proof. The mathematical content, that the minimum of a nonempty finset lies in the finset, is Mathlib's lemma instantiated at a specific set. The library's own definitions here only name that set and its minimum. I did not open the Mathlib file to confirm the exact path of `Finset.min'_mem`. The file path given is where Mathlib normally keeps it (the library imports `Mathlib.Data.Finset.Max`, which re-exports it).

### [`OneMfld.lt_div_self_of_lt_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OneManifold/OneMfld/ClassifyOverlaps.lean#L189-L192) — `lean-pool-0977`

Snippet: `samples/lean-pool/lean-pool-0977.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: div_lt_div_of_pos_left
- **file**: Mathlib/Algebra/Order/GroupWithZero/Basic.lean
- **derivation**: by simpa only [div_one] using div_lt_div_of_pos_left hμ0 hρ0 hρ1
- **explanation**: Mathlib has no strict `lt_div_self` lemma. It does have the non-strict `le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b` in `Mathlib/Algebra/Order/Field/Basic.lean`, which is proved by specialising `div_le_div_of_nonneg_left`. The strict version follows in the same way from `div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c`. Take a := μ, c := ρ and b := 1. This gives μ / 1 < μ / ρ, and `div_one` turns it into μ < μ / ρ. The lemma's typeclass assumptions should hold for NNReal, but I couldn't run Lean to check this. The library proves the result differently, using `lt_div_iff₀` and `mul_lt_of_lt_one_right`.

### [`PiMat.center`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/RepTheory/AutMat.lean#L581-L585) — `lean-pool-0979`

Snippet: `samples/lean-pool/lean-pool-0979.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.center_pi
- **file**: Mathlib/Algebra/Group/Center.lean
- **derivation**: by rw [Set.center_pi]; ext; simp
- **explanation**: `PiMat R ι n` is the library's abbreviation for `Π i, Matrix (n i) (n i) R`. Mathlib's `Set.center_pi` states `center (Π i, A i) = univ.pi fun i ↦ center (A i)` for any family of types with a `Mul` instance. Setting `A i := Matrix (n i) (n i) R` gives the theorem, up to rewriting `univ.pi s` as `{x | ∀ i, x i ∈ s i}` (`Set.mem_univ_pi`, which `simp` handles). The rewrite step is needed because `∀ i ∈ univ, …` is not definitionally the same as `∀ i, …`. That small step is why I classed this as `special_case` rather than `duplicate`. The current proof just calls the library's own lemma `Matrix.pi_center`, and that lemma is proved with `simp_rw [Set.center_pi, Matrix.center]`. So the theorem only uses `Set.center_pi` indirectly.

### [`integrand_bound_on_annulus`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/StepBounds.lean#L769-L784) — `lean-pool-0999`

Snippet: `samples/lean-pool/lean-pool-0999.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: norm_le_norm_add_const_of_dist_le
- **file**: Mathlib/Analysis/Normed/Group/Basic.lean
- **derivation**: (norm_le_norm_add_const_of_dist_le (by rw [dist_eq_norm]; exact hr_bounded t ht_pos ht_lt)).trans_eq (by rw [norm_inv, Complex.norm_real, Real.norm_eq_abs])
- **explanation**: The Mathlib lemma is `norm_le_norm_add_const_of_dist_le : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r`. It is the additive form of `norm_le_norm_add_const_of_dist_le'`, generated by `to_additive`. Here we take a = (γ t - γ t₀)⁻¹ * deriv γ t, b = (↑(t - t₀))⁻¹ and r = C. In ℂ, `dist_eq_norm` turns the hypothesis `hr_bounded t ht_pos ht_lt` into `dist a b ≤ C`. Applying the lemma gives `‖a‖ ≤ ‖b‖ + C`, and the rewrite ‖(↑(t - t₀) : ℂ)⁻¹‖ = |t - t₀|⁻¹ (via `norm_inv`, `Complex.norm_real`, `Real.norm_eq_abs`) turns that into the stated bound. The library's proof gets the same result another way: it uses the reverse triangle inequality `norm_sub_norm_le`, then the same rewrite, then `linarith`. The theorem has no mathematical content beyond this single triangle-inequality lemma with specific a and b. I have not compiled the derivation.


## FLT (Anthropic) (137 flagged)

### [`P2MW.S_ModularCurve_XOneP_eq_zero_of_proj_eq_zero_of_qDivisible_normFreePart_points_twoChartModel_x1_mul.TorusGoodSol.pt_ext_of_isDominant`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_eq_zero_of_proj_eq_zero_of_qDivisible_normFreePart_points_twoChartModel_x1_mul.lean#L218-L222) — `flt-anthropic-0003`

Snippet: `samples/flt-anthropic/flt-anthropic-0003.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.ext_of_isDominant_of_isSeparated
- **file**: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
- **derivation**: haveI := hsep
Subtype.ext (ext_of_isDominant_of_isSeparated f (a.2.trans b.2.symm) ι h)
- **proof_uses_it**: True
- **explanation**: The Mathlib lemma says: if `X` is reduced, `f g : X ⟶ Y`, `s : Y ⟶ Z` is separated, `f ≫ s = g ≫ s`, and `ι : W ⟶ X` is dominant with `ι ≫ f = ι ≫ g`, then `f = g`. The library's `SchemeHomOver t f` is just the subtype `{φ : T ⟶ X // φ ≫ f = t}`, so the property proofs `a.2` and `b.2` give `a.1 ≫ f = b.1 ≫ f`. Take `s := f`. Mathlib's lemma then gives `a.1 = b.1`, and `Subtype.ext` turns that into `a = b`. Besides that one lemma, the proof only uses routine glue: turning the hypothesis `hsep` into an instance and applying `Subtype.ext`. All the mathematical content is in Mathlib's lemma, and the library's current proof already applies it in exactly this way. It is not a verbatim duplicate because the statement is phrased with the library's subtype wrapper rather than with bare morphisms.

### [`P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal.AlgebraicCurve.AbelNecessityProof.sub_mem_of_eventually_sub_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal.lean#L27-L57) — `flt-anthropic-0009`

Snippet: `samples/flt-anthropic/flt-anthropic-0009.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PreconnectedSpace.induction₂'
- **file**: Mathlib/Topology/Connected/Clopen.lean
- **derivation**: PreconnectedSpace.induction₂' (fun a b => φ a - φ b ∈ L) (fun x₀ => (h x₀).mono fun x hx => ⟨by simpa using L.neg_mem hx, hx⟩)
  ⟨fun a b c hab hbc => by simpa using L.add_mem hab hbc⟩ x y
- **explanation**: This is a special case of `PreconnectedSpace.induction₂'`. That lemma says: in a preconnected space, if `P` is a transitive relation and every point `x` has a neighbourhood whose points `y` satisfy both `P x y` and `P y x`, then `P x y` holds for all `x` and `y`.

Take `P a b := φ a - φ b ∈ L`.
- **Neighbourhood condition:** `h` gives `P x x₀` for `x` near `x₀`. Its negation in `L`, together with the simp lemma `neg_sub`, gives `P x₀ x`.
- **Transitivity:** use `L.add_mem` with the simp lemma `sub_add_sub_cancel`.

The library proves the same thing by hand with a clopen-set argument, which is exactly how Mathlib proves `induction₂'`.

An alternative two-line route: map `φ` into `M ⧸ L` and apply `IsLocallyConstant.apply_eq_of_preconnectedSpace` via `IsLocallyConstant.iff_eventually_eq`.

The derivation above has not been compiled. I did not find a Mathlib lemma stated directly for subgroup membership.

### [`P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.AlgebraicCurve.WeierstrassCurve.Affine.algebraMap_polynomial_eq_mk_C`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean#L4792-L4794) — `flt-anthropic-0010`

Snippet: `samples/flt-anthropic/flt-anthropic-0010.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AdjoinRoot.mk_C
- **file**: Mathlib/RingTheory/AdjoinRoot.lean
- **derivation**: (AdjoinRoot.mk_C (f := W.polynomial) p).symm
- **explanation**: This result comes from a single Mathlib lemma by fixing one argument. In Mathlib, `WeierstrassCurve.Affine.CoordinateRing W` is an abbrev for `AdjoinRoot W.polynomial` over the base ring `F[X]`, and `CoordinateRing.mk W` is an abbrev for `AdjoinRoot.mk W.polynomial` (both in `Affine/Point.lean`). `AdjoinRoot.mk_C (x : R) : mk f (C x) = of f x` holds by `rfl`. `AdjoinRoot.algebraMap_eq : algebraMap R (AdjoinRoot f) = of f` is also `rfl`. Taking `R := F[X]` and `f := W.polynomial` in `mk_C` and flipping the equation gives the theorem: `of f p` and `algebraMap F[X] W.CoordinateRing p` are definitionally equal. The library proves it directly by `rfl` and does not cite the lemma. The content is purely definitional either way.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq.TwoPresSol.app_map`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq.lean#L149-L153) — `flt-anthropic-0013`

Snippet: `samples/flt-anthropic/flt-anthropic-0013.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.NatTrans.naturality_apply
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: by simpa using (NatTrans.naturality_apply φ.mapPresheaf (homOfLE hle).op x).symm
- **explanation**: This is a special case of `NatTrans.naturality_apply`, the elementwise naturality lemma for natural transformations between functors into a concrete category: `φ.app Y (F.map f x) = G.map f (φ.app X x)`. Take `φ := φ.mapPresheaf : P.presheaf ⟶ Q.presheaf` and `f := (homOfLE hle).op`, then swap the sides. Since `Scheme.Modules.mapPresheaf_app` holds by `rfl` (`φ.mapPresheaf.app U = φ.app U.unop`), the result is the theorem up to definitional unfolding. The library's proof does the same thing by hand: it takes `φ.mapPresheaf.naturality`, applies both sides to `x` with `congrArg`, and finishes with `simpa`. Mathlib's `Scheme.Modules` API (in `AlgebraicGeometry/Modules/Sheaf.lean`) has no dedicated lemma for this. The theorem is entirely about Mathlib objects and has no library-specific content, which is why I count it as a special case rather than as a general principle applied to the library's own definitions. I have not compiled the derivation; it relies on that definitional unfolding.

### [`P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux.qL_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.lean#L116-L119) — `flt-anthropic-0016`

Snippet: `samples/flt-anthropic/flt-anthropic-0016.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_add
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: simp only [qL, ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ), PowerSeries.coe_add]
- **proof_uses_it**: True
- **explanation**: The library's `qL f` is an abbreviation for `((qExpansion 1 ⇑f : PowerSeries ℂ) : LaurentSeries ℂ)`. Mathlib's `ModularForm.qExpansion_add (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) f g` states `qExpansion h (f + g) = qExpansion h f + qExpansion h g` for modular-form-class elements, possibly of different weights. Our theorem takes the special case h = 1 (side conditions `one_pos` and `one_mem_strictPeriods Γ`), with both forms of the same weight. The remaining glue is routine: unfold `qL`, rewrite the coercion `⇑(f + g)` with `ModularForm.coe_add`, and use additivity of the coercion from power series to Laurent series (`PowerSeries.coe_add`). The library's current one-line proof does exactly this.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.KcRsCellChoice.embS_mulSingle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.lean#L328-L333) — `flt-anthropic-0019`

Snippet: `samples/flt-anthropic/flt-anthropic-0019.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidHom.noncommPiCoprod_mulSingle
- **file**: Mathlib/GroupTheory/NoncommPiCoprod.lean
- **derivation**: MonoidHom.noncommPiCoprod_mulSingle (fun q : ↥SQ => embAt (q : HeightOneSpectrum (𝓞 ℚ))) p x
- **proof_uses_it**: True
- **explanation**: The library defines `embS SQ` as `MonoidHom.noncommPiCoprod (fun p => embAt p) _`. Mathlib's `MonoidHom.noncommPiCoprod_mulSingle` states `noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y`. Taking ϕ := embAt, i := p and y := x, after unfolding `embS`, gives exactly the theorem; `DecidableEq` comes from the theorem's `open scoped Classical`. The current proof applies this lemma directly.

### [`P2MW.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.GaloisRep.MultHalfAux.postComp_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.lean#L89-L95) — `flt-anthropic-0022`

Snippet: `samples/flt-anthropic/flt-anthropic-0022.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgHom.cancel_left
- **file**: Mathlib/Algebra/Algebra/Hom.lean
- **derivation**: fun f g h => WithConv.ext ((AlgHom.cancel_left hψ).mp (congrArg WithConv.ofConv h))
- **explanation**: The library's `postComp ψ f` is defined as `WithConv.toConv (ψ.comp (WithConv.ofConv f))`, so it is just post-composition with ψ wrapped in the `WithConv` type synonym. Mathlib's `AlgHom.cancel_left` states: for injective `f`, `f.comp g₁ = f.comp g₂ ↔ g₁ = g₂`. Apply `WithConv.ofConv` to the hypothesis `postComp ψ f = postComp ψ g`. Since `ofConv (toConv x)` reduces to `x` definitionally, this is the equation `ψ.comp (ofConv f) = ψ.comp (ofConv g)`. `cancel_left` then gives `ofConv f = ofConv g`, and `WithConv.ext` concludes `f = g`. The derivation above was not compiled; it relies on that definitional reduction. The current proof does not use `cancel_left`: it repeats the same argument pointwise with `AlgHom.ext` and `hψ`.

### [`P2MW.S_WeierstrassProjModel_exists_pointEval.ProjWeierstrassDehomog.X_eq_zero_and_Y_ne_zero_of_Z_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassProjModel_exists_pointEval.lean#L25-L35) — `flt-anthropic-0031`

Snippet: `samples/flt-anthropic/flt-anthropic-0031.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean
- **derivation**: ⟨WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz,
  fun hy => hP0 (funext fun i => by fin_cases i <;> simp_all)⟩
- **proof_uses_it**: True
- **explanation**: Borderline special_case. The first conjunct, P 0 = 0, is exactly Mathlib's `X_eq_zero_of_Z_eq_zero` [NoZeroDivisors R] (hP : W'.Equation P) (hPz : P z = 0) : P x = 0, where x = 0, z = 2 and W'.Equation P is by definition eval P W'.polynomial = 0. The library proof already applies this lemma. The second conjunct, P 1 ≠ 0, does not come from Mathlib: the nearest lemma, `Y_ne_zero_of_Z_eq_zero`, assumes nonsingularity, while the theorem assumes P ≠ 0. That conjunct is elementary glue: if P 1 = 0 too, then P = 0 by funext and fin_cases. The derivation is unverified. A strict reading could call this conjunct an auxiliary fact and answer none_found instead. All the substance comes from the one Mathlib lemma.

### [`P2MW.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq.ANb.A_cube_sub_B_sq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq.lean#L158-L189) — `flt-anthropic-0033`

Snippet: `samples/flt-anthropic/flt-anthropic-0033.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq
- **file**: Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean
- **derivation**: rw [← map_pow, ← map_pow, ← map_sub, ← map_ofNat ψ 1728, ← map_mul]; congr 1
exact Subtype.ext (funext fun z => by simp [𝔞, 𝔟, 𝔡, ofMF, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]; ring)
- **explanation**: The theorem says E₄³ − E₆² = 1728·Δ, stated for the elements 𝔞 = E₄, 𝔟 = E₆ and 𝔡 = Δ of the library's subalgebra `niceSubalgebra`, after applying the library's algebra hom ψ (q-expansion viewed as a Laurent series). Mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` states the same identity pointwise: `discriminant z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728`.

The suggested derivation uses only routine steps:
- the hom laws (`map_pow`, `map_sub`, `map_mul`, `map_ofNat`) pull everything inside ψ;
- `Subtype.ext` and `funext` reduce the goal to a pointwise identity, which Mathlib's lemma gives;
- `ring` then clears the division by 1728.

So the mathematical content is exactly Mathlib's lemma, moved along ψ. The library's proof does not use it: it redoes the argument from scratch, computing q-coefficients 0 and 1 and applying a weight-12 dimension result. Caveat: I could not compile the two-line derivation. The `simp` step depends on how the coercions of `ofMF` and `CuspForm.discriminant` unfold, so it may need minor adjustment.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.VbUnrq.eval_map_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.lean#L290-L293) — `flt-anthropic-0055`

Snippet: `samples/flt-anthropic/flt-anthropic-0055.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.eval_map_apply
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: (Polynomial.eval_map_apply (p := mO) W.toValuationSubring.subtype x).symm
- **explanation**: The library theorem is a special case of `Polynomial.eval_map_apply`, which states `(p.map f).eval (f x) = f (p.eval x)` for any ring homomorphism `f : R →+* S`. Take `f` to be the subring inclusion `W.toValuationSubring.subtype`. Then `f x` is by definition the coercion `(x : F')`, and `f (mO.eval x)` is the coercion of `mO.eval x`. So the library theorem is that lemma read right to left, with `f` set to this particular map; hence `special_case` rather than `duplicate`. In the lemma `f` and `x` are explicit and `p` is implicit, so the derivation passes `p := mO` by name. The library's current proof does not use this lemma: it rewrites with `Polynomial.eval_map` and then applies `Polynomial.eval₂_hom`.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.C_eq_algebraMap
- **file**: Mathlib/RingTheory/HahnSeries/Multiplication.lean
- **derivation**: by rw [HahnSeries.C_eq_algebraMap]
- **explanation**: Mathlib's `HahnSeries.C_eq_algebraMap : C = algebraMap R R⟦Γ⟧` holds for any commutative semiring `R` and ordered `Γ`, and it is proved by `rfl`. `LaurentSeries L` is by definition `HahnSeries ℤ L`, so the library's theorem is this ring-hom equality with `Γ := ℤ` and `R := L`, applied to an element `c`. I could not run Lean, so the suggested one-line `rw` is unchecked. It should work: after rewriting `C`, both sides are definitionally equal and `rw` closes the goal with `rfl`. `RingHom.congr_fun HahnSeries.C_eq_algebraMap c` would also do. The library's current proof goes another way, through `algebraMap_laurentSeries_eq_single` and `HahnSeries.C_apply`.

### [`P2MW.S_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul.B5w.val_scalar_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul.lean#L121-L127) — `flt-anthropic-0067`

Snippet: `samples/flt-anthropic/flt-anthropic-0067.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.diagonal_mul
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
- **explanation**: This is a special case of `Matrix.diagonal_mul`, which states `(diagonal d * M) i j = d i * M i j`. Take `d = fun _ => (c : R)` and `M = ↑g`. Three rewrites turn the theorem's left side into that form: `Units.val_mul` takes the coercion through the product in GL, `Matrix.GeneralLinearGroup.coe_scalar` turns the GL scalar into `Matrix.scalar (Fin 2) ↑c`, and `Matrix.scalar_apply` (true by `rfl`) turns that into `diagonal fun _ => ↑c`. After this, `diagonal_mul` closes the goal, because `(fun _ => ↑c) i` reduces to `↑c` by beta reduction. I have not compiled this derivation. The library's proof takes a different route, through `Matrix.smul_eq_diagonal_mul` and `Matrix.smul_apply`. Mathlib has no lemma stated directly for an entry of `GeneralLinearGroup.scalar u * g`. I checked the `GeneralLinearGroup` files and searched for names like `scalar_mul_apply`.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq.WGenH.inseparable_genericPoint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq.lean#L24-L25) — `flt-anthropic-0080`

Snippet: `samples/flt-anthropic/flt-anthropic-0080.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion
- **file**: Mathlib/AlgebraicGeometry/FunctionField.lean
- **derivation**: Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion ψ).symm
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `genericPoint_eq_of_isOpenImmersion`. That lemma says: if `f : X ⟶ Y` is an open immersion between irreducible schemes, then `f (genericPoint X) = genericPoint Y`.

Here `ψ : Mdl.C ⟶ Mdl.C` is an isomorphism, so Mathlib's instance makes it an open immersion, and the curve `Mdl.C` is irreducible. The lemma then gives `ψ.base (genericPoint Mdl.C) = genericPoint Mdl.C`. Mathlib's `f x` is notation for `f.base x`, so this is the same expression. Flipping it with `.symm` and applying `Inseparable.of_eq` gives the theorem.

The library's proof does `rw [base_genericPoint]`, and its local lemma `base_genericPoint` is just `genericPoint_eq_of_isOpenImmersion ψ`. So the current proof already uses this declaration, through a one-line local wrapper.

I could not run Lean, so the suggested one-line derivation has not been compiled.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le.SVDGlue.continuous_det`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le.lean#L109-L115) — `flt-anthropic-0086`

Snippet: `samples/flt-anthropic/flt-anthropic-0086.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.continuous_det
- **file**: Mathlib/Topology/Algebra/Group/Matrix.lean
- **derivation**: Matrix.GeneralLinearGroup.continuous_det
- **explanation**: Mathlib's `Matrix.GeneralLinearGroup.continuous_det` states `Continuous (det : GL n R → Rˣ)` for any commutative topological ring `R` with `[IsTopologicalRing R]` and a finite index type `n` with decidable equality. The library's theorem is this statement for `n = Fin 2` and `R` the p-adic completion of ℚ, which is a topological field and so meets these assumptions. The library writes the map as the lambda `fun h => det h`, which is just the eta-expanded form of `det`. Mathlib's lemma has universally quantified arguments, so it applies to the library's setting as it is, without specializing anything. The library's proof re-derives the result through `Units.continuous_iff` instead of citing the lemma. I did not run Lean, so the one-line derivation has not been compiled.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: iterate_map_mul
- **file**: Mathlib/Algebra/Group/Hom/Defs.lean
- **derivation**: iterate_map_mul (AutomorphicForm.sigmaTensor K L (HeightOneSpectrum.adicCompletion K v) σ) i x y
- **explanation**: Mathlib's `iterate_map_mul` says that for any `f : F` with `[MulHomClass F M M]`, `f^[n] (x * y) = f^[n] x * f^[n] y`. In the library, `sigmaTensor` is defined as a `RingHom` `L ⊗[K] A →+* L ⊗[K] A`, so it is an instance of `MulHomClass`. Taking `f := σE` gives exactly the theorem. Nothing about `sigmaTensor` beyond its being a multiplicative map is used. The current proof does not use this lemma: it rewrites the iterate as a power (`sigmaTensor_pow`) and then applies `map_mul`.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_eq_zero_iff
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: by rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
   exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective
- **proof_uses_it**: True
- **explanation**: The library defines `qC F := ofPowerSeries ℤ ℂ (qExpansion 1 F)`, so `qC` is just Mathlib's q-expansion pushed into Laurent series. Mathlib's `ModularForm.qExpansion_eq_zero_iff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) : qExpansion h f = 0 ↔ f = 0` gives the actual result once you take h = 1 and Γ = Γ m M'. All that is left is to unfold `qC` and use the fact that the embedding `ofPowerSeries` is injective (`map_eq_zero_iff` with `HahnSeries.ofPowerSeries_injective`). That injectivity step is routine glue, not a second result of substance. The library's current proof already does exactly this, so the derivation above is that proof.

### [`P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero.WeierstrassCurve.M5HD2.psCoeff_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero.lean#L313-L315) — `flt-anthropic-0107`

Snippet: `samples/flt-anthropic/flt-anthropic-0107.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: PowerSeries.coeff_coeToMvPowerSeries
- **file**: Mathlib/RingTheory/PowerSeries/Basic.lean
- **derivation**: (PowerSeries.coeff_coeToMvPowerSeries n).symm
- **explanation**: The Mathlib lemma `PowerSeries.coeff_coeToMvPowerSeries {f : R⟦X⟧} (n : ℕ) : MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n` states the same equation with its two sides swapped. It needs only `[Semiring R]`, which is weaker than the theorem's `[CommRing R]`. `PowerSeries R` is an abbrev for `MvPowerSeries Unit R`, so no coercion is involved, and Mathlib proves the lemma by `rfl`. The library's proof does not use this lemma: it rewrites with `PowerSeries.coeff_def` instead.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Ψ₂Sq_ne_zero
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
- **derivation**: (𝓦p p).Ψ₂Sq_ne_zero (four_ne_zero_Rp p hp2)
- **explanation**: Mathlib's `WeierstrassCurve.Ψ₂Sq_ne_zero (h : (4 : R) ≠ 0) : W.Ψ₂Sq ≠ 0` holds for any Weierstrass curve over a commutative ring where 4 ≠ 0. The library's theorem is this lemma with W instantiated to the library's curve `𝓦p p` over `Rp p = MvPolynomial (Fin 5) (ZMod p)`. The hypothesis 4 ≠ 0 comes from the library's own lemma `four_ne_zero_Rp p hp2`, which the current proof already calls; the derivation uses nothing else. The current proof does not cite the Mathlib lemma: it computes coeff 3 of Ψ₂Sq by hand. Mathlib proves that step as `coeff_Ψ₂Sq`/`coeff_Ψ₂Sq_ne_zero` in the same file. One caveat: discharging the hypothesis with a library lemma rather than one of the listed glue tactics stretches the "routine glue" rule a little. The Mathlib lemma still carries all of the polynomial content.

### [`P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop.AnnulusG1.le_map_sum_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop.lean#L266-L277) — `flt-anthropic-0140`

Snippet: `samples/flt-anthropic/flt-anthropic-0140.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddValuation.map_le_sum
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: tsub_le_iff_right.mp (v.map_le_sum fun k hk => tsub_le_iff_right.mpr (h k hk))
- **explanation**: AddValuation.map_le_sum says: if g ≤ v (f i) for all i ∈ s, then g ≤ v (∑ i ∈ s, f i). The library's theorem is the same statement with every bound shifted by + w in ℕ∞. Because ℕ∞ has the OrderedSub instance, tsub_le_iff_right turns n ≤ x + w into n - w ≤ x and back. So the theorem is map_le_sum with g := n - w, with tsub_le_iff_right applied on both sides. The verdict counts tsub_le_iff_right as routine glue (a generic order lemma used like a rewrite); if it is not counted, the answer would be none_found. The derivation was not compiled. The library's proof does induction on s with the two-term rule v.map_add instead of using map_le_sum.

### [`P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two.R1CDWidth.natCast_mem_asIdeal_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two.lean#L50-L53) — `flt-anthropic-0148`

Snippet: `samples/flt-anthropic/flt-anthropic-0148.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Rat.HeightOneSpectrum.natGenerator_dvd_iff
- **file**: Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean
- **derivation**: rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]
- **proof_uses_it**: True
- **explanation**: I found no Mathlib lemma that states this result word for word. The closest is `Rat.HeightOneSpectrum.natGenerator_dvd_iff`, which holds for any `R` with `[IsIntegralClosure R ℤ ℚ]`. It says `natGenerator v ∣ n ↔ ↑n ∈ v.asIdeal.map (IsIntegralClosure.intEquiv R)`. Taking `R = 𝓞 ℚ` gives the library's theorem, except that membership is stated in the image of the ideal under the ring isomorphism `intEquiv : 𝓞 ℚ ≃+* ℤ`, not in `w.asIdeal` itself. Two generic glue lemmas bridge that gap. `map_natCast` rewrites `(n : ℤ)` as `intEquiv (n : 𝓞 ℚ)`, and `Ideal.apply_mem_of_equiv_iff` says `f x ∈ I.map f ↔ x ∈ I`. Both are general facts about homomorphisms, so the mathematical content sits in `natGenerator_dvd_iff`. The library's current one-line proof is exactly this rewrite. Mathlib's own proof of `valuation_equiv_padicValuation`, in the same file, uses the same three-lemma combination inline. I grepped Mathlib for `natGenerator` and `primesEquiv`, and both occur only in this file. This is a borderline call: if `Ideal.apply_mem_of_equiv_iff` is counted as a second substantive lemma rather than glue, the verdict would be `none_found`.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback.FunFamilySpread.appLE_appLE_of_comp_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback.lean#L48-L52) — `flt-anthropic-0153`

Snippet: `samples/flt-anthropic/flt-anthropic-0153.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
- **file**: Mathlib/AlgebraicGeometry/Scheme.lean
- **derivation**: subst hc
rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma, and the current proof already uses that lemma. In Mathlib, `Scheme.Hom.appLE_comp_appLE` says `g.appLE U V e₁ ≫ f.appLE V W e₂ = (f ≫ g).appLE U W _`. It is tagged `@[reassoc]` but not `@[elementwise]`, and my search of Mathlib found no ready-made `_apply` form.

The library theorem is that same equation applied to an element `z`, with the composite `c ≫ s` renamed to `d` through the hypothesis `hc`. Once `subst hc` removes `d`, the only change is applying the morphism equation to `z` with `comp_apply`. The two proofs that `W` lies in the preimage are equal by proof irrelevance, so `rw` closes the goal. The library's two-line proof is exactly this derivation.

### [`P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve.UnivPropC.monic_ΦJ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.lean#L65-L67) — `flt-anthropic-0158`

Snippet: `samples/flt-anthropic/flt-anthropic-0158.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.Monic.map
- **file**: Mathlib/Algebra/Polynomial/Monic.lean
- **derivation**: data.monic.map _
- **proof_uses_it**: True
- **explanation**: `ΦJ K data` is an abbrev for `data.Φ.map (eval₂RingHom (Int.castRingHom (jAdj K)) (jGen K))`. Mathlib's `Polynomial.Monic.map (f : R →+* S) (hp : Monic p) : Monic (p.map f)` says that mapping a monic polynomial along a ring hom gives a monic polynomial. Taking `p := data.Φ`, which is monic by `data.monic`, and `f :=` that evaluation ring hom gives exactly the theorem. The library's proof is already this one-line application. The only thing the theorem adds beyond Mathlib is unfolding the library's own definition `ΦJ`.

### [`P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.TQStruct.isNoetherianRing_of_finite`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.lean#L74-L77) — `flt-anthropic-0194`

Snippet: `samples/flt-anthropic/flt-anthropic-0194.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: IsNoetherianRing.of_finite
- **file**: Mathlib/RingTheory/Noetherian/Basic.lean
- **derivation**: IsNoetherianRing.of_finite 𝒪 A
- **explanation**: This duplicates `IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S] [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S`. It states the same result under weaker assumptions. In the library's setting the commutative rings are rings, and `[Algebra 𝒪 A]` provides both the `Module 𝒪 A` instance and `IsScalarTower 𝒪 A A` (via `IsScalarTower.right`). So Mathlib's lemma applies directly to `𝒪` and `A` without specialising any of its arguments. The library's proof does not cite this lemma. Instead it repeats the lemma's own proof, `isNoetherian_of_tower R inferInstance`.

### [`P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le.LanglandsTunnell.CubicInduction.RaySupplyK1.idA_mulA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le.lean#L159-L161) — `flt-anthropic-0206`

Snippet: `samples/flt-anthropic/flt-anthropic-0206.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.one_mul
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: show Matrix.of idA * Matrix.of e = Matrix.of e; rw [of_idA, Matrix.one_mul]
- **proof_uses_it**: True
- **explanation**: In the library, `Arr` is defined as `Fin 3 → Fin 3 → ℝ` and `mulA e e'` is defined as `Matrix.of e * Matrix.of e'`. The library lemma `of_idA` shows that `idA` is the identity matrix `1`. With those definitions unfolded, the theorem is just `1 * M = M` for real 3×3 matrices. That is Mathlib's `Matrix.one_mul` with the matrix `Matrix.of e`. The current proof already uses this: it rewrites with `of_mulA` and `of_idA`, then applies `Matrix.one_mul`. This is a borderline call. The derivation also relies on the library lemma `of_idA`, the small fact that `idA` equals `1`, which can also be shown by `ext; simp [idA, Matrix.one_apply]`. Apart from that wrapper, all of the mathematical content is `Matrix.one_mul`.

### [`P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.TraceDepletion.denom_SL_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.lean#L429-L432) — `flt-anthropic-0209`

Snippet: `samples/flt-anthropic/flt-anthropic-0209.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UpperHalfPlane.denom_ne_zero
- **file**: Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean
- **derivation**: by rw [← ModularGroup.denom_apply]; exact UpperHalfPlane.denom_ne_zero _ τ
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) (z : ℍ) : denom g z ≠ 0`, with `g` taken to be the image of `γ : SL(2, ℤ)` in `GL (Fin 2) ℝ`. `ModularGroup.denom_apply`, which holds by `rfl`, rewrites `denom γ τ` as `γ 1 0 * τ + γ 1 1` with integer casts, and that is exactly the expression in the library's statement. The library's proof already does this: one `rw [← ModularGroup.denom_apply]`, then `denom_ne_zero`. I found no Mathlib lemma stated directly for SL(2, ℤ) with explicit integer entries. The general `linear_ne_zero` lemma would also need a separate proof that the bottom row is nonzero.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.finrank_fiber_eq_finrank
- **file**: Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean
- **derivation**: by rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, Module.finrank_eq_of_rank_eq hrank]
- **explanation**: The Mathlib lemma `Ideal.finrank_fiber_eq_finrank` (in `Module`, with `[IsDomain R]`, `[Module.Flat R M]`, `[Module.Finite R M]`) states `finrank p.ResidueField (p.Fiber M) = finrank R M` for every prime `p`. Its proof first rewrites the left side to `rankAtStalk M ⟨p, _⟩`, so its real content is that, over a domain, a finite flat module has rank `finrank R M` at every stalk. That is also the content of the library theorem.

The derivation needs three rewrites:
1. `Module.rankAtStalk_eq` turns `rankAtStalk M p` into the finrank of the fiber.
2. `Ideal.finrank_fiber_eq_finrank` turns that into `finrank S M`. The theorem's `FinitePresentation` assumption gives the `Module.Finite` instance this lemma needs.
3. `Module.finrank_eq_of_rank_eq hrank` turns `Module.rank S M = n` into `finrank S M = n`.

Steps 1 and 3 are standard rewrites that restate the same quantity in another form. Step 2 is the substantive one. Because the derivation uses two other Mathlib lemmas besides it, the classification is borderline.

The library's proof does not use this lemma. It argues directly: since Spec S is connected, the locally constant rank function takes the same value everywhere as at the generic point ⊥, and it computes the rank there with `IsLocalization.rank_eq` and `IsLocalizedModule.rank_eq`.

### [`P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.NoethModel17.fg_restrictScalars`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean#L67-L72) — `flt-anthropic-0241`

Snippet: `samples/flt-anthropic/flt-anthropic-0241.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.FiniteType.trans
- **file**: Mathlib/RingTheory/FiniteType.lean
- **derivation**: (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 (.trans ((Subalgebra.fg_iff_finiteType _).1 h₁) ((Subalgebra.fg_iff_finiteType _).1 h₂))
- **proof_uses_it**: True
- **explanation**: The math here is that finite type is transitive in the tower ℤ → R₁ → T. Mathlib states this as `Algebra.FiniteType.trans`: if `FiniteType R S`, `FiniteType S A` and `IsScalarTower R S A`, then `FiniteType R A`. Take R = ℤ, S = ↥R₁ and A = ↥T; the scalar tower instance is found automatically. The only other ingredient is `Subalgebra.fg_iff_finiteType` (`S.FG ↔ Algebra.FiniteType R S`), used in both directions to move between `Subalgebra.FG` and `FiniteType`. That is the routine translation between the two equivalent finiteness notions. The library's proof is exactly this composition, spread over four `have`/`exact` lines.

I found no Mathlib lemma stated directly for subalgebras in the form `(T.restrictScalars R).FG` from `R₁.FG` and `T.FG`. `Subalgebra.FG.restrictScalars` and `Submodule.FG.restrictScalars` are different results: they need `Module.Finite` hypotheses. Other candidates I read: `Algebra.fg_trans'`, which is the same transitivity stated with `⊤` subalgebras, and the FG lemmas in `RingTheory/Adjoin/FG.lean`.

The one-line derivation is my compression of the library's proof and has not been compiled. It relies on `↥(T.restrictScalars ℤ)` being definitionally equal to `↥T`, which the library's final `exact` step already depends on.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.DualB.inv_ofReal_cpow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.lean#L233-L235) — `flt-anthropic-0243`

Snippet: `samples/flt-anthropic/flt-anthropic-0243.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Complex.inv_cpow_ofReal_nonneg
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean
- **derivation**: by rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
- **explanation**: The theorem says that for 0 < r, ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s). Mathlib's `Complex.inv_cpow_ofReal_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℂ) : ((a : ℂ)⁻¹) ^ r = (a ^ r : ℂ)⁻¹` already has this content, under the weaker hypothesis 0 ≤ a. The statements differ only by routine rewrites: `Complex.ofReal_inv` moves the inverse outside the coercion on the left, and `Complex.cpow_neg` (x ^ (-y) = (x ^ y)⁻¹) turns the right side into an inverse. So the one-line `rw` above proves the theorem. The current proof works one level lower: it applies `Complex.inv_cpow` (the lemma behind `inv_cpow_ofReal_nonneg`) and proves the side condition on `arg` by hand. Strictly, no argument is instantiated, so this is not a pure special case. It is not a duplicate either, because the two sides of the equation are in different forms. I chose `special_case` because the derivation is a one-line `rw` using only allowed glue.

### [`P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.SmoothPointDVR.primeCompl_le_nonZeroDivisors`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.lean#L183-L187) — `flt-anthropic-0264`

Snippet: `samples/flt-anthropic/flt-anthropic-0264.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.primeCompl_le_nonZeroDivisors
- **file**: Mathlib/RingTheory/Ideal/Operations.lean
- **derivation**: (𝔮 hker hab).primeCompl_le_nonZeroDivisors
- **explanation**: Mathlib's `Ideal.primeCompl_le_nonZeroDivisors` says that for any prime ideal `P` of a commutative semiring `R` with `[NoZeroDivisors R]`, `P.primeCompl ≤ nonZeroDivisors R`. Here `R` is `A K x y`, a subalgebra of the field `F`, so it inherits `NoZeroDivisors`. `P` is `𝔮 hker hab`, which is prime by the scoped instance `𝔮_isPrime`. So the theorem is that lemma with `R` and `P` instantiated, and one term proves it. The library's proof does not cite the lemma; it repeats the same argument by hand with `mem_nonZeroDivisors_of_ne_zero`.

### [`P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv.GaloisRepAdic.LCSol.det_apply_baseChangeAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_ordinaryCondition_of_isEquiv.lean#L92-L97) — `flt-anthropic-0265`

Snippet: `samples/flt-anthropic/flt-anthropic-0265.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.det_baseChange
- **file**: Mathlib/LinearAlgebra/Charpoly/BaseChange.lean
- **derivation**: letI : Algebra A B := φ.toAlgebra
exact LinearMap.det_baseChange (ρ.ρ σ)
- **proof_uses_it**: True
- **explanation**: Mathlib's `LinearMap.det_baseChange` says `LinearMap.det (f.baseChange A) = algebraMap R A (LinearMap.det f)`. In the library, `GaloisRepAdic.baseChangeAlong φ hφ ρ` is defined, under `letI : Algebra A B := φ.toAlgebra`, as the representation on `B ⊗[A] ρ.V` sending `σ` to `(ρ.ρ σ).baseChange B`. With that algebra structure, `algebraMap A B` is `φ`. So once the definition is unfolded, the theorem is exactly `LinearMap.det_baseChange` with `R := A`, `A := B`, the algebra structure taken to be `φ.toAlgebra`, and `f := ρ.ρ σ`.

The current proof already does this: it sets up the algebra instance, uses `show` to restate the goal in unfolded form, and applies `LinearMap.det_baseChange`. The `show` step is only a definitional restatement, and `exact` should check it by unfolding without it, though I could not run Lean to confirm the two-line version compiles.

The only things specific to the library are its definition `baseChangeAlong` and treating `φ` as an algebra map. All of the mathematical content comes from the Mathlib lemma.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.LeftInverse.injective
- **file**: Init/Data/Function.lean
- **derivation**: Function.LeftInverse.injective (g := fun x => b (b x)) hb
- **explanation**: Lean core's `Function.LeftInverse.injective : LeftInverse g f → Injective f`, with `LeftInverse g f := ∀ x, g (f x) = x`. Taking g := fun x => b (b x) and f := b, the hypothesis `LeftInverse g b` is definitionally `∀ x, b (b (b x)) = x`, which is exactly `hb`, so the lemma gives `Injective b`. The library's proof does the same thing by hand: it applies b ∘ b to both sides and simplifies with hb. I also searched for iterate-based injectivity lemmas such as `Injective.of_comp_iterate`. I found only `Injective.iterate`, which goes the other way, and a linear-map version that doesn't apply here.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finsupp.filter_sum
- **file**: Mathlib/Data/Finsupp/Basic.lean
- **derivation**: by classical; unfold PlaceSpecialization.fstDiv; exact Finsupp.filter_sum _ _
- **explanation**: `Divisor K F` is an abbreviation for `Place K F →₀ ℤ`, and `P.fstDiv D` is defined as `D.filter P.IsStrictFst`, with a classical decidability instance. Mathlib's `Finsupp.filter_sum` says `(∑ a ∈ s, f a).filter p = ∑ a ∈ s, (f a).filter p`. Taking `p := P.IsStrictFst` and unfolding `fstDiv` gives exactly this theorem. The library's proof instead does its own induction on `s`, using `Finsupp.filter_zero` and its own lemma `fstDiv_add`. I could not compile the one-line derivation. It assumes the instance found under `classical` matches the classical instance inside `fstDiv`, which it should, because `IsStrictFst` is a plain `def` and instance search will not unfold it. If the instances don't line up, `simpa [PlaceSpecialization.fstDiv] using Finsupp.filter_sum s f` or `convert` should do the job.

### [`P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile.K7RA5c.exp_neg_le_factorial_mul_inv_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile.lean#L285-L294) — `flt-anthropic-0274`

Snippet: `samples/flt-anthropic/flt-anthropic-0274.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.pow_div_factorial_le_exp
- **file**: Mathlib/Analysis/Complex/Exponential.lean
- **derivation**: simpa [Real.exp_neg, inv_div, div_eq_mul_inv] using inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp x hx.le k)
- **proof_uses_it**: True
- **explanation**: Borderline call. Mathlib's `Real.pow_div_factorial_le_exp (hx : 0 ≤ x) (n) : x ^ n / n ! ≤ exp x` is the same inequality as the theorem. Taking inverses of both sides gives `exp(-x) = (exp x)⁻¹ ≤ (x^k/k!)⁻¹ = k! * (x^k)⁻¹` for `x > 0`. No argument is specialised: the theorem is an algebraic rearrangement restricted to `x > 0`, which needs `inv_anti₀` (an inequality flip under inversion, treated here as routine glue) plus simp rewriting. If `inv_anti₀` is not counted as glue, the verdict would be `none_found`. The library's proof already applies this lemma and rearranges it in a calc block. The suggested derivation has not been compiled. I grepped Mathlib for a direct statement `exp (-x) ≤ k!/x^k`, for `exp (-…) ≤` statements, `x ^ k * exp (-x)` bounds and `factorial` next to `exp`, and found none.

### [`groupCohomology.comap_fixingSubgroup_eq_ker`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GroupCohomology_LevelSubgroup.lean#L9-L14) — `flt-anthropic-0288`

Snippet: `samples/flt-anthropic/flt-anthropic-0288.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.restrictNormalHom_ker
- **file**: Mathlib/FieldTheory/Galois/Basic.lean
- **derivation**: by rw [← IntermediateField.restrictNormalHom_ker F, MonoidHom.comap_ker]; rfl
- **proof_uses_it**: True
- **explanation**: The Mathlib lemma `IntermediateField.restrictNormalHom_ker` (Mathlib/FieldTheory/Galois/Basic.lean) says `(restrictNormalHom E).ker = E.fixingSubgroup` for `E : IntermediateField K L` with `[Normal K E]`. The library's theorem takes K = ℚ and L = AlgebraicClosure ℚ, then pulls both sides back along `r`. The only other step is `MonoidHom.comap_ker`, which states `g.ker.comap f = (g.comp f).ker` and is proved by `rfl`. That is plain bookkeeping about kernels and adds no mathematical content. Equivalently, the result is `(congrArg (Subgroup.comap r) (IntermediateField.restrictNormalHom_ker F)).symm`, up to definitional unfolding. The library's current proof already does exactly this rewrite. I found no Mathlib lemma stated directly for comap along an arbitrary homomorphism `r`, so I classify it as a special case rather than a duplicate.

### [`P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.X1BoundedDenominators.disc_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean#L189-L194) — `flt-anthropic-0303`

Snippet: `samples/flt-anthropic/flt-anthropic-0303.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SlashInvariantForm.slash_action_eqn''
- **file**: Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean
- **derivation**: SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `slash_action_eqn''` says that for any slash-invariant form `f` on a subgroup `Γ` with `HasDetOne`, and any `γ ∈ Γ`, we have `f (γ • z) = denom γ z ^ k * f z`. Taking `f := CuspForm.discriminant` (a cusp form of weight 12 on `𝒮ℒ`), `γ := ↑α` and `z := τ` gives the theorem. The only gap is notation: `CuspForm.coe_discriminant` (the coercion of the cusp form to Δ) and `ModularGroup.sl_moeb` (the SL action equals the action of its image in GL) both hold by `rfl`. Because of that, the lemma's output should close the goal directly, without the `rw`. I have not checked this, since I cannot run Lean. If it fails, the library's current `rw ... at this; exact this` works. The library's proof already applies this lemma. I also checked Discriminant.lean, and Mathlib has no lemma specific to Δ for its value at `α • τ`; it only has the T- and S-invariance lemmas.

### [`P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight.Ws31.C3Glue.L5_deriv_congr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight.lean#L274-L276) — `flt-anthropic-0307`

Snippet: `samples/flt-anthropic/flt-anthropic-0307.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Set.EqOn.deriv
- **file**: Mathlib/Analysis/Calculus/Deriv/Basic.lean
- **derivation**: Set.EqOn.deriv h hU hs₀
- **explanation**: The Mathlib lemma `Set.EqOn.deriv` says: for any nontrivially normed field 𝕜, if `s.EqOn f g` and `IsOpen s`, then `s.EqOn (deriv f) (deriv g)`. Since `Set.EqOn f g s` unfolds to `∀ x ∈ s, f x = g x`, the hypothesis `h` already has the right type. The conclusion `s.EqOn (deriv F) (deriv G)` unfolds to `∀ x ∈ U, deriv F x = deriv G x`. Applying it to `s₀` and `hs₀` gives exactly the library's statement. The only differences are presentation (unfolding `EqOn`, and taking the point `s₀` and its membership proof as explicit arguments) and Mathlib's more general field 𝕜, which covers ℂ without instantiating anything. The library's current proof uses `Filter.EventuallyEq.deriv_eq` instead.

### [`P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.UnitTensorDescent.baseChange_cancelBaseChange`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.lean#L118-L133) — `flt-anthropic-0311`

Snippet: `samples/flt-anthropic/flt-anthropic-0311.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
- **file**: Mathlib/LinearAlgebra/TensorProduct/Tower.lean
- **derivation**: LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R (FractionRing R) K h) u
- **explanation**: The Mathlib lemma states `lTensor _ _ f ∘ₗ cancelBaseChange R A B M N = (cancelBaseChange R A B M Q) ∘ₗ lTensor _ _ (lTensor _ _ f)`, i.e. that `cancelBaseChange` is natural in `N`. Take A := FractionRing R, B := M := K, N := Q := T and f := h, then evaluate both sides at `u`. The result is the library's statement, up to definitional unfolding. `LinearMap.baseChange A f` is defined as `AlgebraTensorModule.map id f`, and `AlgebraTensorModule.lTensor A M f` is `map id f`, so `h.baseChange K` and `h.baseChange (FractionRing R)` agree definitionally with the `lTensor` maps in the lemma (`baseChange_eq_ltensor` is proved by `rfl`). The outer `LinearMap.lTensor K` also matches the coercion of `AlgebraTensorModule.lTensor` (`coe_lTensor` is proved by `rfl`). The required instances (IsScalarTower R K K, SMulCommClass (FractionRing R) K K, Algebra (FractionRing R) K) are already needed to state the library's theorem. Since M and B are both set to K, this is an instantiation, so the verdict is special_case. The library proves it by tensor induction plus simp instead of using this lemma. I could not run Lean, so the one-line derivation is unchecked and relies on these definitional unfoldings going through.

### [`P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.ALLiP.map_int_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.lean#L41-L43) — `flt-anthropic-0314`

Snippet: `samples/flt-anthropic/flt-anthropic-0314.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.map_mul
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: Matrix.map_mul
- **explanation**: The theorem is a special case of `Matrix.map_mul`. That lemma states `(L * M).map f = L.map f * M.map f` for any `f` in a `NonUnitalRingHomClass`, with `L`, `M` and `f` implicit. Setting `f := algebraMap ℤ ℝ` and taking 2×2 integer matrices gives exactly this theorem, so the proof can be `Matrix.map_mul`. The current proof does not use it: it rewrites to `RingHom.mapMatrix` and then applies the generic `map_mul`.

### [`P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.P2mSemilin.inv_comp_base`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.lean#L102-L105) — `flt-anthropic-0319`

Snippet: `samples/flt-anthropic/flt-anthropic-0319.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.inv_comp_eq
- **file**: Mathlib/CategoryTheory/Iso.lean
- **derivation**: B.inv_comp_eq.mpr hB.symm
- **proof_uses_it**: True
- **explanation**: Mathlib's `Iso.inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g` states the theorem's whole content. Take α := B, f := c and g := c ≫ e. Then `.mpr` applied to `hB.symm : c = B.hom ≫ c ≫ e` gives `B.inv ≫ c = c ≫ e`, because `≫` associates to the right. The theorem is this general category-theory fact used for schemes. The current proof already uses this lemma, with an extra `simpa only [Category.assoc]` step. That step is probably redundant, since `B.hom ≫ c ≫ e` already parses as `B.hom ≫ (c ≫ e)`. I have not compiled the shorter derivation.

### [`P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.SlopeLaw0.coe_smul_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.lean#L621-L626) — `flt-anthropic-0331`

Snippet: `samples/flt-anthropic/flt-anthropic-0331.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.smul_def
- **file**: Mathlib/Algebra/Algebra/Defs.lean
- **derivation**: by rw [Algebra.smul_def]; rfl
- **proof_uses_it**: True
- **explanation**: This is a borderline call. The theorem is `Algebra.smul_def` (`r • x = algebraMap R A r * x`) applied to the algebra `modularFunctionFieldBar (1 * q)` over `AlgebraicClosure ℚ`, with the scalar `↑c`. The equation is then pushed through the coercion into `LaurentSeries`, where `rfl` closes the goal because multiplication in the subobject is the restricted multiplication. Nothing in the statement depends on a property of `modularFunctionFieldBar`, so all the content comes from the generic Mathlib lemma. The current proof already does exactly this: `rw [Algebra.smul_def]; rfl`. One could argue instead for `none_found`, on the grounds that `Algebra.smul_def` is a basic structural axiom, much like the excluded homomorphism laws. I chose `special_case` because the content here sits entirely in that lemma and not in the library's own definitions. I did not search for alternative matches, such as a coercion-of-smul lemma for subalgebras or intermediate fields.

### [`P2MW.S_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0.NumberField.DiscPermSol.Frame.le_exp_neg_one_of_lt_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0.lean#L147-L153) — `flt-anthropic-0339`

Snippet: `samples/flt-anthropic/flt-anthropic-0339.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WithZero.lt_mul_exp_iff_le
- **file**: Mathlib/Algebra/Order/GroupWithZero/Canonical.lean
- **derivation**: (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp (by rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero])
- **explanation**: This is a special case of `WithZero.lt_mul_exp_iff_le`. That lemma says: for `x y : ℤᵐ⁰` with `y ≠ 0`, `x < y * exp 1 ↔ x ≤ y`. Take `y = exp (-1)`, which is nonzero by `exp_ne_zero`. Then `exp (-1) * exp 1` equals `exp 0`, which is `1`, by `exp_add` and `exp_zero`. Both of those lemmas are proved by `rfl`. So the hypothesis `t < 1` becomes `t < exp (-1) * exp 1`, and the forward direction of the iff gives `t ≤ exp (-1)`. I have not compiled the derivation. The library's proof does not use this lemma: it splits into the cases `t = 0` and `t = exp z`, then uses `exp_lt_exp`, `exp_le_exp` and `omega`.

### [`P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.RATIOCOVER.exists_eq_smul_of_mem_center`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.lean#L71-L74) — `flt-anthropic-0345`

Snippet: `samples/flt-anthropic/flt-anthropic-0345.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Basic.lean
- **derivation**: obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
exact ⟨a, by rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar` says that, for any finite index type `n` and commutative ring `R`, `g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (Matrix.scalar n)`. That means some `a` has `scalar n a = g.val`. The library's theorem takes `n = Fin 2` and a field `K`, and writes the scalar matrix as `a • 1` instead. The two forms are equated by rewriting with `Matrix.scalar_apply` and `Matrix.smul_one_eq_diagonal`. Because the index type is fixed to `Fin 2`, this counts as a special case rather than a duplicate. The library's current proof is already exactly this two-line derivation.

### [`P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.AlgebraicCurve.PeriodLatticeIsLatticeProof.linearIndependent_of_card_le_of_span_eq_top`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.lean#L39-L47) — `flt-anthropic-0347`

Snippet: `samples/flt-anthropic/flt-anthropic-0347.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: linearIndependent_of_top_le_span_of_card_le_finrank
- **file**: Mathlib/LinearAlgebra/Dimension/OrzechProperty.lean
- **derivation**: linearIndependent_of_top_le_span_of_card_le_finrank (by rw [Subtype.range_coe, hspan]) (by simpa [Fintype.card_coe] using hcard)
- **proof_uses_it**: True
- **explanation**: The library theorem is a special case of the Mathlib lemma `linearIndependent_of_top_le_span_of_card_le_finrank`. That lemma works over any ring with the Orzech property, for any family `b : ι → M` with `[Fintype ι]`: if `⊤ ≤ span R (Set.range b)` and `Fintype.card ι ≤ finrank R M`, then `LinearIndependent R b`. The library theorem takes `R := ℝ`, `ι := ↥(s : Set E)` and `b := Subtype.val`. The only glue needed is routine: `Set.range Subtype.val = ↑s` (`Subtype.range_coe`) to turn `hspan` into the span hypothesis, and `Fintype.card ↥↑s = s.card` (`Fintype.card_coe`) to turn `hcard` into the cardinality hypothesis. The library's current proof already applies this lemma in exactly this way. I read the lemma's statement in `Mathlib/LinearAlgebra/Dimension/OrzechProperty.lean`, and a grep for other `card_le_finrank` lemmas in `Mathlib/LinearAlgebra` found no Finset- or Set-specific version that would make this an exact duplicate.

### [`P2MW.S_ModularCurve_transcendental_coeffEmb_jq.DivUSol.isScalarTower_rat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_transcendental_coeffEmb_jq.lean#L128-L132) — `flt-anthropic-0368`

Snippet: `samples/flt-anthropic/flt-anthropic-0368.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: IsScalarTower.rat
- **file**: Mathlib/Algebra/Module/Rat.lean
- **derivation**: @IsScalarTower.rat (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) _ _ _ Algebra.toModule Algebra.toModule
- **explanation**: I found Mathlib's instance `IsScalarTower.rat` in `Mathlib/Algebra/Module/Rat.lean`. For any ring `R` and additive group `M` with `[Module R M] [Module ℚ R] [Module ℚ M]`, it gives `IsScalarTower ℚ R M`. Here `R = AlgebraicClosure ℚ` and `M = LaurentSeries (AlgebraicClosure ℚ)`. Mathlib needs only module structures, which is weaker than the algebra structures the theorem uses, and the instance applies to this setting directly.

The theorem fixes the scalar actions to `Algebra.toSMul`. `Algebra.toModule` defines its scalar action as `Algebra.toSMul`, so passing `Algebra.toModule` explicitly for both rational module instances gives exactly the stated actions. Since everything goes through definitional unfolding, this rests on reasoning about the definitions; I could not run Lean to check that it elaborates.

The library's proof does not use this instance. It goes through `IsScalarTower.of_algebraMap_eq` and uses the fact that ring maps out of `ℚ` are unique (`Subsingleton.elim`).

### [`P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.ModularCurve.QExpN.liftPerm_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean#L140-L142) — `flt-anthropic-0373`

Snippet: `samples/flt-anthropic/flt-anthropic-0373.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.Perm.decomposeFin_symm_apply_zero
- **file**: Mathlib/GroupTheory/Perm/Fin.lean
- **derivation**: Equiv.Perm.decomposeFin_symm_apply_zero 0 e
- **proof_uses_it**: True
- **explanation**: The library's `liftPerm ℓ e` is defined as `Equiv.Perm.decomposeFin.symm (0, e)`. Mathlib's lemma states `Equiv.Perm.decomposeFin.symm (p, e) 0 = p` for any `p : Fin (n+1)`. Taking `n = ℓ` and `p = 0` gives `liftPerm ℓ e 0 = 0` after unfolding the definition. The current proof is exactly this application.

### [`P2MW.S_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn.TwS6a.P_succ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn.lean#L672-L674) — `flt-anthropic-0375`

Snippet: `samples/flt-anthropic/flt-anthropic-0375.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: List.prod_range_succ
- **file**: Mathlib/Algebra/BigOperators/Group/List/Basic.lean
- **derivation**: by unfold P; exact List.prod_range_succ _ n
- **explanation**: The library defines P K L A σ δ n as ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod. Mathlib's List.prod_range_succ holds in any monoid M (commutativity not needed): ((range n.succ).map f).prod = ((range n).map f).prod * f n. Taking f := fun i => (⇑(sigmaGL K L A σ))^[i] δ in the monoid GL (Fin 2) (L ⊗[K] A) gives P_succ exactly; n + 1 and n.succ are definitionally equal. The current proof uses simp only to re-derive the lemma with the same rewrites Mathlib's own proof uses, instead of citing it. Not checked by compiling.

### [`P2MW.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq.AdelicSlice.s1_exists_intCast_of_forall_valuation_le_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq.lean#L714-L720) — `flt-anthropic-0386`

Snippet: `samples/flt-anthropic/flt-anthropic-0386.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
- **file**: Mathlib/RingTheory/DedekindDomain/AdicValuation.lean
- **derivation**: obtain ⟨r, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
exact ⟨Rat.ringOfIntegersEquiv r, by simp⟩
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `mem_integers_of_valuation_le_one` says that for any Dedekind domain R with fraction field K, if `v.valuation K x ≤ 1` for every height-one prime v, then `x ∈ (algebraMap R K).range`. Taking R = 𝓞 ℚ and K = ℚ gives `q = algebraMap (𝓞 ℚ) ℚ r` for some r, which is the theorem's content. What remains is glue: passing from 𝓞 ℚ to ℤ through `Rat.ringOfIntegersEquiv`. That side goal should close with `simp`, using the simp lemma `Rat.ringOfIntegersEquiv_apply_coe` (`(ringOfIntegersEquiv z : ℚ) = algebraMap (𝓞 ℚ) ℚ z`). I could not compile the two-line derivation. The library's proof already applies this lemma and then does the 𝓞 ℚ → ℤ step with its own helper, `s1_exists_intCast_eq`.

### [`P2MW.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.CosetDict.pr_mem_integers`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.lean#L111-L111) — `flt-anthropic-0389`

Snippet: `samples/flt-anthropic/flt-anthropic-0389.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: natCast_mem
- **file**: Mathlib/Algebra/Ring/Subsemiring/Defs.lean
- **derivation**: natCast_mem _ _
- **explanation**: Mathlib's `natCast_mem` says `(n : R) ∈ s` for any natural number `n` and any `s : S` where `S` has an `AddSubmonoidWithOneClass S R` instance. `adicCompletionIntegers ℚ v` is a `ValuationSubring` of the completion `𝕂`, and valuation subrings form a `SubringClass`, which supplies that instance. Taking `s := 𝓞v` and `n := pr v` gives the theorem. The current proof does not use it: it goes through the file's own `natCast_mem_integers`, which proves the fact by hand from `mem_adicCompletionIntegers`, `valued_algebraMap` and `valuation_le_one`.

### [`P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve.WUniqLevelP.not_mem_nonunits_of_inv_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.lean#L105-L107) — `flt-anthropic-0394`

Snippet: `samples/flt-anthropic/flt-anthropic-0394.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValuationSubring.mem_nonunits_iff_or
- **file**: Mathlib/RingTheory/Valuation/ValuationSubring.lean
- **derivation**: fun hn => (A.mem_nonunits_iff_or.mp hn).elim ha0 (· h)
- **explanation**: The library's theorem follows from one direction of a Mathlib lemma. Mathlib's `ValuationSubring.mem_nonunits_iff_or` (line 565) states `x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A`. Our theorem takes `a ≠ 0` and `a⁻¹ ∈ A` and concludes `a ∉ A.nonunits`. If `a` were in `A.nonunits`, `.mp` would give `a = 0 ∨ a⁻¹ ∉ A`, and both cases contradict a hypothesis. So the proof is `.mp` followed by eliminating the `Or`, which is routine glue on that single lemma. A tactic version such as `by rw [ValuationSubring.mem_nonunits_iff_or]; simp [ha0, h]` should also work, though I did not run either form since Lean is not available here. The current proof does not use the Mathlib lemma. It goes through the library's own `mem_nonunits_iff'`, which states `a ∈ A.nonunits ↔ a ∈ A ∧ (a = 0 ∨ a⁻¹ ∉ A)` and is proved from Mathlib's `mem_nonunits_iff_exists_mem_maximalIdeal`. This is the contrapositive of one direction rather than an instantiation, so the verdict could be read as either `duplicate` or `special_case`; I chose `special_case` because a one-line argument is needed.

### [`P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.CycBaseKummerSurj.levelGal_surjective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.lean#L55-L63) — `flt-anthropic-0399`

Snippet: `samples/flt-anthropic/flt-anthropic-0399.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgEquiv.restrictNormalHom_surjective
- **file**: Mathlib/FieldTheory/Normal/Basic.lean
- **derivation**: (AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL)) (E := AlgebraicClosure ℚ)).comp (IntermediateField.fixingSubgroupEquiv K).surjective
- **proof_uses_it**: True
- **explanation**: I'm calling this a special case of `AlgEquiv.restrictNormalHom_surjective`, though it's a borderline call. The library defines `levelGal K L hKL` as `(AlgEquiv.restrictNormalHom (levelField K L hKL)).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom`. That is, the Mathlib restriction map Gal(Q̄/K) → Gal(levelField/K), with K.fixingSubgroup first identified with Gal(Q̄/K) by a Mathlib equivalence.

Surjectivity of this composite is Mathlib's `AlgEquiv.restrictNormalHom_surjective` (with F = K, K₁ = levelField, E = Q̄), composed with the surjectivity of a `MulEquiv`. That second step is generic glue. The current proof does exactly this: it applies `restrictNormalHom_surjective`, then cancels the equivalence with `MulEquiv.apply_symm_apply`.

The one-line derivation I give relies on `MonoidHom.comp` unfolding to function composition by definition. I couldn't run Lean to check it. It assumes the instance `Normal K (AlgebraicClosure ℚ)` is found, as it is in the current proof.

Why borderline: `levelGal` is the library's own definition. But it is only a composite of two Mathlib maps, so the mathematical content still comes from `restrictNormalHom_surjective`. I found no Mathlib lemma that states surjectivity of this exact composite directly.

### [`P2MW.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.HeckeEis.BolAux.coeff_pderiv_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean#L22-L48) — `flt-anthropic-0401`

Snippet: `samples/flt-anthropic/flt-anthropic-0401.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.coeff_pderiv
- **file**: Mathlib/Algebra/MvPolynomial/PDeriv.lean
- **derivation**: by rw [coeff_pderiv]; push_cast; ring
- **explanation**: Mathlib's `MvPolynomial.coeff_pderiv` works over any `CommSemiring R`, for any variable type `σ` and any index `i`. It states `coeff m (pderiv i p) = coeff (m + single i 1) p * (m i + 1)`. Setting `σ := Fin 2` and `i := 1` gives the library statement, up to two cosmetic differences: the order of the multiplication, and whether the `+ 1` is cast as `((d 1 + 1 : ℕ) : K)` or written `(↑(d 1) + 1)`. `push_cast` and `ring` handle both. The library proves the result again from scratch by induction on monomials, so it does not use the Mathlib lemma.

### [`P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.PDivStep2R.resAut_mk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.lean#L295-L296) — `flt-anthropic-0406`

Snippet: `samples/flt-anthropic/flt-anthropic-0406.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.quotient_map_mkₐ
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.quotient_map_mkₐ (f := σ'.toAlgHom) (maxI_le_comap p σ')
- **explanation**: This is a borderline case. `resAut p σ'` is defined as exactly `Ideal.quotientMapₐ (maxI p R) σ'.toAlgHom (maxI_le_comap p σ')`. Mathlib's `Ideal.quotient_map_mkₐ` says `quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x)`, and its proof is `rfl`. Take I = J = maxI p R and f = σ'.toAlgHom, and unfold `resAut`. Since `Quotient.mkₐ` agrees definitionally with `Quotient.mk` and `σ'.toAlgHom s` with `σ' s`, this gives the theorem. The library proves it with `rfl` directly, without citing the Mathlib lemma. The theorem is just the computation rule of the library's thin wrapper `resAut`, and all of its mathematical content is the Mathlib lemma specialised to a particular ideal and automorphism. One could instead argue that its content lies in the library's own definition, which would make it `none_found`. The derivation above was not compiled; `rfl`, as the library uses, works as well.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one.GLUEbc.discreteTopology_of_isFinite`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one.lean#L178-L184) — `flt-anthropic-0414`

Snippet: `samples/flt-anthropic/flt-anthropic-0414.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage
- **file**: Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean
- **derivation**: isDiscrete_univ_iff.mp (by simpa using g.isDiscrete_preimage (s := Set.univ) (isDiscrete_univ_iff.mpr ⟨Subsingleton.elim _ _⟩))
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `Scheme.Hom.isDiscrete_preimage`. That lemma says: if `f` is locally quasi-finite and `s` is a discrete subset of the target (`IsDiscrete s`), then `IsDiscrete (f ⁻¹' s)`. A finite morphism is locally quasi-finite through a low-priority instance in the same file.

To get the theorem, take `s = Set.univ` in `Spec K`. The space `Spec K` is discrete because it has a single point. Then `isDiscrete_univ_iff` turns `IsDiscrete univ` into `DiscreteTopology`, and `Set.preimage_univ` simplifies the preimage of `univ`. The library's proof is exactly this, spread over four lines.

The proof does not use `IsAlgClosed K`. There is a second route: `IsLocallyArtinian.of_locallyQuasiFinite g` gives `IsLocallyArtinian Z`, and the instance `IsLocallyArtinian.discreteTopology` then gives the discrete topology. That route chains two Mathlib results, so I cite the single-lemma route above. I could not run Lean, so the one-line derivation has not been compiled.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one.dflip_mul_scalar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one.lean#L1757-L1763) — `flt-anthropic-0416`

Snippet: `samples/flt-anthropic/flt-anthropic-0416.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.scalar_commute
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: (Matrix.GeneralLinearGroup.scalar_commute t dflip).symm
- **explanation**: This is a special case of a Mathlib lemma. `Matrix.GeneralLinearGroup.scalar_commute` (over any commutative ring `R`) states `scalar n u * A = A * scalar n u` for every `u : Rˣ` and every `A : GL n R`. Take `n := Fin 3`, `R := A` (a field, so a commutative ring), `u := t` and the matrix `A := dflip`. Applying `.symm` then gives exactly `dflip * scalar (Fin 3) t = scalar (Fin 3) t * dflip`. The theorem is just this one instance of the general fact that scalar matrices commute with every element of GL. The library's current proof does not use the lemma: it computes the 3×3 matrix product entry by entry with `fin_cases`.

### [`P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve.ESDescent.conj_mem'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.lean#L200-L203) — `flt-anthropic-0421`

Snippet: `samples/flt-anthropic/flt-anthropic-0421.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.normal_subgroupOf_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Basic.lean
- **derivation**: by simpa using (Subgroup.normal_subgroupOf_iff hle).mp hn γ (δ : SL(2, ℤ))⁻¹ hγ (Γ.inv_mem δ.2)
- **explanation**: The theorem is a special case of `Subgroup.normal_subgroupOf_iff`. That lemma says: if `H ≤ K`, then `(H.subgroupOf K).Normal` holds exactly when `∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H`. Take `H = Γ'`, `K = Γ`, `h = γ` and `k = δ⁻¹`. This gives `δ⁻¹ * γ * δ⁻¹⁻¹ ∈ Γ'`, and `simpa` rewrites `δ⁻¹⁻¹` to `δ` using `inv_inv`. The membership side goal `δ⁻¹ ∈ Γ` is `Γ.inv_mem δ.2`.

The current proof does not cite the Mathlib lemma directly. It goes through the library's own `conj_mem`, which is the `k = δ` case of the same lemma (`(Subgroup.normal_subgroupOf_iff hle).mp hn γ δ hγ δ.2`), applied to `δ⁻¹`, followed by `simpa`. So it relies on the lemma only through that intermediate result, which is why `proof_uses_it` is `false`.

The derivation is reasoned from the lemma's statement only; it has not been compiled.

### [`P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.K6A.continuous_sG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.lean#L247-L262) — `flt-anthropic-0426`

Snippet: `samples/flt-anthropic/flt-anthropic-0426.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Continuous.units_map
- **file**: Mathlib/Topology/Algebra/Monoid.lean
- **derivation**: Continuous.units_map _ (continuous_id.matrix_map (continuous_congr K L v σ))
- **explanation**: The library defines `sG` as `Matrix.GeneralLinearGroup.map` applied to the ring hom `Algebra.TensorProduct.congr σ AlgEquiv.refl`. In Mathlib that `map` is defined as `Units.map (RingHom.mapMatrix f).toMonoidHom`. `Continuous.units_map` states that `Units.map f` is continuous whenever the monoid hom `f` is continuous. Here `f` is the entrywise matrix map, which is continuous by `Continuous.matrix_map` applied to the library's `continuous_congr`. The current proof does not cite `Continuous.units_map`: it re-proves its body (`Units.continuous_iff` on both components, plus a `map_inv` rewrite for the inverse). The derivation was written from the sources and not compiled. The `[IsTopologicalRing ...]` assumption is not needed for it.

### [`P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three.ModularCurve.O4Eng.transcendental_of_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three.lean#L121-L123) — `flt-anthropic-0431`

Snippet: `samples/flt-anthropic/flt-anthropic-0431.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: transcendental_algebraMap_iff
- **file**: Mathlib/RingTheory/Algebraic/Basic.lean
- **derivation**: (transcendental_algebraMap_iff (algebraMap E L).injective).mp h
- **explanation**: This is a special case of a general Mathlib lemma. `transcendental_algebraMap_iff` states that if `algebraMap S A` is injective, then `Transcendental R (algebraMap S A a) ↔ Transcendental R a`. Take `R := K`, `S := E` (the intermediate field) and `A := L`. The coercion `(z : L)` is definitionally `algebraMap E L z`, and the injectivity side condition holds because `algebraMap E L` is a ring hom between fields. The library's proof instead negates `IntermediateField.isAlgebraic_iff`, which is the algebraic counterpart of the same fact. A second route would be `Subalgebra.transcendental_iff_transcendental_val`, applied to `E.toSubalgebra`.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.WhittakerPS2Ext.psi_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.lean#L205-L208) — `flt-anthropic-0435`

Snippet: `samples/flt-anthropic/flt-anthropic-0435.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddChar.val_isUnit
- **file**: Mathlib/Algebra/Group/AddChar.lean
- **derivation**: (ψ.val_isUnit a).ne_zero
- **explanation**: I found no Mathlib lemma that states `ψ a ≠ 0` directly, but the result follows in one line from `AddChar.val_isUnit`. That lemma says that for any `[AddGroup A] [Monoid M]` and any `φ : AddChar A M`, the value `φ a` is a unit. Here `A` is the adic completion `F`, which is an additive group, and `M` is `ℂ`. Since `ℂ` is nontrivial, `IsUnit.ne_zero` then gives `ψ a ≠ 0`. The verdict is special_case rather than duplicate because Mathlib states the result as `IsUnit`, and the step from there to `≠ 0` is the glue. The library's proof does not use this lemma. It goes through its own `psi_neg_mul_self` (presumably `ψ (-a) * ψ a = 1`): it substitutes `h : ψ a = 0` to get `0 = 1`, a contradiction. A related Mathlib lemma, `AddChar.coe_ne_zero`, only says the whole function `ψ` is not the zero function, which is weaker than the statement here.

### [`P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.MvPolynomial.CrossingQuotient.Resolution.torusLift_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.lean#L319-L321) — `flt-anthropic-0463`

Snippet: `samples/flt-anthropic/flt-anthropic-0463.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsLocalization.Away.lift_eq
- **file**: Mathlib/RingTheory/Localization/Away/Basic.lean
- **derivation**: IsLocalization.Away.lift_eq _ _ c
- **proof_uses_it**: True
- **explanation**: I judged this a special case of `IsLocalization.Away.lift_eq`. The library defines `torusLift a b h` (line 313) directly as `IsLocalization.Away.lift (algebraMap W (CrossingQuotient W t) t)`, with `g := (algebraMap W (Localization.Away t)).comp (lift t a b h).toRingHom`. Mathlib's `IsLocalization.Away.lift_eq` states `lift x hg (algebraMap R S a) = g a`. Instantiating it with this particular `x` and `g` gives exactly the theorem: the right-hand side `g c` unfolds by definition to `algebraMap W _ (lift t a b h c)`. The library's proof is already the one-line application `IsLocalization.Away.lift_eq _ _ c`. The only library-specific part is the choice of `g`; the mathematical content is Mathlib's rule for evaluating a lift out of a localization. One could argue the other way, since this is just the defining equation of the library's own `torusLift`, which the instructions say does not count. I chose `special_case` because the result is a direct instance of the Mathlib lemma.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_range_sup_range_comp_eq_top_of_isPullback_chartVRing.F2AlphaE.algebraMap_pow_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_range_sup_range_comp_eq_top_of_isPullback_chartVRing.lean#L541-L545) — `flt-anthropic-0468`

Snippet: `samples/flt-anthropic/flt-anthropic-0468.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.mk_singleton_self
- **file**: Mathlib/RingTheory/Ideal/Quotient/Basic.lean
- **derivation**: by rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (chartVRing 𝒪 r) (Avn 𝒪 r π n), Ideal.Quotient.algebraMap_eq, map_pow]
   exact Ideal.Quotient.mk_singleton_self _
- **explanation**: This is a special case of Mathlib's `Ideal.Quotient.mk_singleton_self`, which says `mk (Ideal.span {x}) x = 0`. `Avn 𝒪 r π n` is an abbreviation, defined in this file, for the quotient `chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}`. So the theorem says that the generator of this principal ideal is zero in the quotient, which is the Mathlib lemma with `x := (algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)`. The derivation keeps the library's own `rw` steps, which rewrite the algebra map through the scalar tower into `Ideal.Quotient.mk`, and then closes the goal with the Mathlib lemma instead of `Ideal.Quotient.eq_zero_iff_mem` and `Ideal.subset_span`. I could not compile this derivation. This is a borderline call: the result is little more than unfolding the library's definition `Avn`, but the mathematical fact used (an element is zero modulo the ideal it generates) is Mathlib's lemma.

### [`P2MW.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw.Ws26T4.isLocalHom_algebraMap_intClosure`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw.lean#L115-L126) — `flt-anthropic-0474`

Snippet: `samples/flt-anthropic/flt-anthropic-0474.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RingHom.IsIntegral.isLocalHom
- **file**: Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean
- **derivation**: RingHom.IsIntegral.isLocalHom (algebraMap_isIntegral_iff.mpr inferInstance) fun a b h =>
  Subtype.ext ((algebraMap ℚ_[q] Kw).injective (congrArg (fun x : integralClosure ℤ_[q] Kw => (x : Kw)) h))
- **explanation**: Mathlib's `RingHom.IsIntegral.isLocalHom` says that an injective integral ring hom `f : R →+* S` is a local hom, with no locality assumptions. Here `R = ℤ_[q]` and `S = integralClosure ℤ_[q] Kw`. Integrality comes from the instance `integralClosure.AlgebraIsIntegral`, turned into `RingHom.IsIntegral` by `algebraMap_isIntegral_iff`. Injectivity holds because the map, followed by the coercion to `Kw`, is `ℤ_[q] → ℚ_[q] → Kw`. `ℤ_[q]` is a subtype of `ℚ_[q]` (so `Subtype.ext` applies), and a map out of a field is injective. The library's own proof `rfl` (`h2`) shows the maps agree definitionally after coercing to `PadicAlgCl q`; I am assuming the same holds at `Kw`, which I could not check because I cannot run Lean. With a `FaithfulSMul ℤ_[q] (integralClosure ℤ_[q] Kw)` instance, the instance `Algebra.IsIntegral.isLocalHom` would give the result directly. The `IsLocalRing` hypothesis is not needed. The library instead proves it with p-adic norms (units have norm 1).

### [`P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering.INF.coeff_coe_ratSmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.lean#L59-L64) — `flt-anthropic-0478`

Snippet: `samples/flt-anthropic/flt-anthropic-0478.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.coeff_smul
- **file**: Mathlib/RingTheory/HahnSeries/Addition.lean
- **derivation**: HahnSeries.coeff_smul (r := c) (x := (x : LaurentSeries ℚ)) (a := n)
- **explanation**: The theorem is `HahnSeries.coeff_smul` (`(r • x).coeff a = r • x.coeff a`, proved by `rfl`) with Γ = ℤ, R = V = ℚ. The rest is glue that holds by definition. First, the coercion out of the intermediate field commutes with the scalar action; the library's own `h1` proves this by `rfl`. Second, the field instance on Hahn series sets `qsmul := (· • ·)`, so the division-ring ℚ-action is definitionally the coefficientwise HahnSeries action. Mathlib checks this with `example : (instSMul : SMul ℚ R⟦Γ⟧) = Rat.smulDivisionRing := rfl` in HahnSeries/Summable.lean. Third, `c • q = c * q` on ℚ holds by definition. So Mathlib's lemma, applied as a term, should close the goal up to definitional unfolding; I could not compile this to confirm, and a plain `rfl` should also work. The library proof goes the long way instead: it uses `Rat.smul_def`, rewrites the ℚ-cast as `HahnSeries.C`, and then applies `HahnSeries.coeff_single_zero_mul`.

### [`NumberField.ArchIdele.exists_above`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NumberField_ArchimedeanIdeleModule.lean#L152-L153) — `flt-anthropic-0480`

Snippet: `samples/flt-anthropic/flt-anthropic-0480.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: NumberField.InfinitePlace.comap_surjective
- **file**: Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean
- **derivation**: InfinitePlace.comap_surjective v
- **proof_uses_it**: True
- **explanation**: This is a duplicate. Mathlib's `comap_surjective` states `Function.Surjective (comap · (algebraMap k K))` for fields `k` and `K` with `[Algebra k K] [Algebra.IsAlgebraic k K]`. Unfolding `Function.Surjective` gives exactly `∀ v, ∃ w, w.comap (algebraMap k K) = v`, which is the library theorem. Mathlib's assumptions are weaker: when both fields are number fields, `Algebra.IsAlgebraic` is found automatically by instance search, so the lemma applies in the theorem's own setting without instantiating anything. The library's proof is already exactly this lemma applied to `v`.

### [`P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.LayerPlumbing.isOpen_setOf_isUnit_mixedSpace`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.lean#L105-L112) — `flt-anthropic-0482`

Snippet: `samples/flt-anthropic/flt-anthropic-0482.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Units.isOpen
- **file**: Mathlib/Analysis/Normed/Ring/Units.lean
- **derivation**: Units.isOpen
- **explanation**: `Units.isOpen` says `IsOpen {x : R | IsUnit x}` for any `[NormedRing R] [HasSummableGeomSeries R]`. `mixedSpace L` is an `abbrev` for `({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)`, a product of finite Pi types over ℝ and ℂ. That type is a complete normed ring through the Pi and Prod instances, so the instance `[NormedRing R] [CompleteSpace R] : HasSummableGeomSeries R` in `Mathlib/Analysis/SpecificLimits/Normed.lean` applies. Taking R := mixedSpace L in `Units.isOpen` gives the theorem. The topology coming from the normed-ring structure should be the product topology by definition. I could not run Lean, so whether `exact Units.isOpen` elaborates directly is not checked. The library's proof does not use `Units.isOpen`: it rewrites the set as an intersection of sets where the coordinates are nonzero.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ.StalkConstr.padicInt_exists_nat_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ.lean#L303-L308) — `flt-anthropic-0483`

Snippet: `samples/flt-anthropic/flt-anthropic-0483.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PadicInt.appr_spec
- **file**: Mathlib/NumberTheory/Padics/RingHoms.lean
- **derivation**: obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n r)
exact ⟨r.appr n, r', by rw [← hr']; ring⟩
- **explanation**: The Mathlib lemma `PadicInt.appr_spec (n : ℕ) : ∀ x : ℤ_[p], x - appr x n ∈ Ideal.span {(p : ℤ_[p]) ^ n}` says that every p-adic integer differs from a natural number, its approximation `appr x n`, by a multiple of p^n. The library theorem is the existential form of this statement. Take k = r.appr n. `Ideal.mem_span_singleton` turns the ideal membership into a divisibility, which gives r' with r - k = p^n * r', and `ring` finishes the goal. The library's proof does not use `appr_spec`. It goes through `PadicInt.toZModPow`, `PadicInt.ker_toZModPow` and `Ideal.mem_span_singleton'` instead.

### [`P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion.P2MKcDegC6.addOrderOf_div_nsmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_moduliPlace_restrictAlong_inclusion.lean#L43-L48) — `flt-anthropic-0486`

Snippet: `samples/flt-anthropic/flt-anthropic-0486.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: addOrderOf_nsmul_addOrderOf_div
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: by subst hg; exact addOrderOf_nsmul_addOrderOf_div hN hMN
- **explanation**: This is a duplicate of `addOrderOf_nsmul_addOrderOf_div`, the additive version of `orderOf_pow_orderOf_div`. Mathlib generates it from that lemma with `@[to_additive]`; the name was not grepped, it follows from how `to_additive` renames, so it is inferred. The multiplicative lemma is stated for any monoid `G`: if `orderOf x ≠ 0` and `n ∣ orderOf x`, then `orderOf (x ^ (orderOf x / n)) = n`. The additive version therefore says that if `addOrderOf x ≠ 0` and `n ∣ addOrderOf x`, then `addOrderOf ((addOrderOf x / n) • x) = n`, for any additive monoid. That covers the theorem's `AddCommGroup` setting. The library's theorem says the same thing, except that it names the order `N` and adds the hypothesis `hg : addOrderOf g = N`. That is only a difference in presentation, and substituting `hg` removes it. The library's current proof does not use this lemma: it works through `addOrderOf_nsmul'`, `Nat.gcd_eq_right` and `Nat.div_div_self`.

### [`P2MW.S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd.GalTqSol.isTorsionFree_end`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd.lean#L287-L294) — `flt-anthropic-0489`

Snippet: `samples/flt-anthropic/flt-anthropic-0489.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.instIsTorsionFreeLinearMap (anonymous instance `instance [Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M')`, line 106)
- **file**: Mathlib/Algebra/Module/LinearMap/Basic.lean
- **derivation**: inferInstance
- **explanation**: Mathlib has an anonymous instance in namespace `LinearMap` (Mathlib/Algebra/Module/LinearMap/Basic.lean, line 106): `instance [Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M')`. Its context needs `[Semiring S] [Module S M] [Module S M'] [SMulCommClass R' S M']`. Its proof is `coe_injective.moduleIsTorsionFree _ coe_smul`.

The library's theorem is the case S = R = R' = 𝒪, σ₁₂ = RingHom.id, M = M' = V, since `Module.End 𝒪 V` is `V →ₗ[𝒪] V`. The required `SMulCommClass 𝒪 𝒪 V` holds automatically because 𝒪 is commutative. Mathlib does not need the library's `IsDomain 𝒪` hypothesis.

I call this a special case rather than a duplicate because M and M' are both set to V and S is set to the base ring. Because Mathlib states it as an instance, `inferInstance` should prove the theorem; I could not run Lean to confirm this. The instance has no explicit name, so the name I give is my guess at the one Lean generates.

The library's proof does not use this instance: it checks torsion-freeness by hand, pointwise with `LinearMap.ext` and `isSMulRegular`.

### [`P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.mem_Jtor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.lean#L98-L99) — `flt-anthropic-0493`

Snippet: `samples/flt-anthropic/flt-anthropic-0493.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.mem_torsionBy_iff
- **file**: Mathlib/Algebra/Module/Torsion/Basic.lean
- **derivation**: Submodule.mem_torsionBy_iff _ _
- **proof_uses_it**: True
- **explanation**: This is a special case of `Submodule.mem_torsionBy_iff`. The library defines `Jtor M H p n` as `(Submodule.torsionBy ℤ (JH M H) ((p ^ n : ℕ) : ℤ)).toAddSubgroup`. Membership in `toAddSubgroup` is definitionally membership in the submodule, so the theorem is Mathlib's `Submodule.mem_torsionBy_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0` with `R := ℤ` and `a := ((p ^ n : ℕ) : ℤ)`. Mathlib's lemma is proved by `Iff.rfl`. `Jtor` is only a thin wrapper around `torsionBy`, and the library's current proof is exactly this one application.

### [`P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two.E150I.isDiscreteValuationRing_of_ringEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two.lean#L87-L98) — `flt-anthropic-0498`

Snippet: `samples/flt-anthropic/flt-anthropic-0498.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: RingEquivClass.isDiscreteValuationRing
- **file**: Mathlib/RingTheory/DiscreteValuationRing/Basic.lean
- **derivation**: RingEquivClass.isDiscreteValuationRing e
- **explanation**: Mathlib states: for `A`, `B` commutative domains with `[IsDiscreteValuationRing A]` and any `e : E` where `[EquivLike E A B] [RingEquivClass E A B]`, `B` is an `IsDiscreteValuationRing`. The library theorem is the same result for `e : A ≃+* B`. `A ≃+* B` already has a `RingEquivClass` instance, so Mathlib's lemma applies to `e` as it is: the implicit `E` is simply inferred to be `A ≃+* B`, and nothing has to be specialised. The library proves the result by hand instead, rebuilding the principal-ideal, local-ring and not-a-field parts.

### [`P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.isHomogeneous_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean#L86-L88) — `flt-anthropic-0499`

Snippet: `samples/flt-anthropic/flt-anthropic-0499.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.mem_homogeneousSubmodule
- **file**: Mathlib/RingTheory/MvPolynomial/Homogeneous.lean
- **derivation**: (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2
- **proof_uses_it**: True
- **explanation**: Mathlib's `MvPolynomial.mem_homogeneousSubmodule (n) (p) : p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n`, which is proved by `Iff.rfl`, already states this result. The theorem is its forward direction, instantiated at σ = Fin (n+1), R = k and p = ↑F, and applied to the membership proof `F.2`. The library's proof is exactly that one-line application, so it is just Mathlib's lemma restated for elements of the subtype. Because membership unfolds by definition to `IsHomogeneous`, `F.2` alone would also prove it.

### [`P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.ModularCurve.DivisorFunction.ofComplex_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.lean#L29-L29) — `flt-anthropic-0509`

Snippet: `samples/flt-anthropic/flt-anthropic-0509.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: UpperHalfPlane.ofComplex_apply
- **file**: Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean
- **derivation**: ofComplex_apply τ
- **proof_uses_it**: True
- **explanation**: The theorem is a duplicate of Mathlib's `UpperHalfPlane.ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z`. The two statements are identical apart from the variable name, and the library's proof just applies this lemma. I did not check that `ofComplex` in the library resolves to `UpperHalfPlane.ofComplex`. It almost certainly does, because `UpperHalfPlane` is opened and the proof applies `ofComplex_apply` directly.

### [`P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective.HeisC4a.Tlin_single`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective.lean#L62-L68) — `flt-anthropic-0513`

Snippet: `samples/flt-anthropic/flt-anthropic-0513.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Fintype.linearCombination_apply_single
- **file**: Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean
- **derivation**: (Fintype.linearCombination_apply_single B (fun x => schrod δ d B ω (γ (Heis.theta x)) v) y 1).trans (one_smul _ _)
- **explanation**: The library's `Tlin δ d B ω γ v` is a `B`-linear map `(HH δ → B) →ₗ[B] (HH δ → B)` whose `toFun` is `c ↦ ∑ x, c x • schrod δ d B ω (γ (Heis.theta x)) v`. Mathlib's `Fintype.linearCombination R v : (α → R) →ₗ[R] M` is defined with exactly the same `toFun`, `f ↦ ∑ i, f i • v i`. So `Tlin` is definitionally `Fintype.linearCombination B (fun x => schrod δ d B ω (γ (Heis.theta x)) v)`. Mathlib's `Fintype.linearCombination_apply_single` says `Fintype.linearCombination R v (Pi.single i r) = r • v i`. Taking `R := B`, the vector family above, `i := y` and `r := 1`, and then rewriting with `one_smul`, gives the theorem. The library's current proof does not cite this lemma: it unfolds the sum and uses `Finset.sum_eq_single` by hand. I have not compiled the derivation. It relies on `Tlin ... (Pi.single y 1)` and `Fintype.linearCombination ... (Pi.single y 1)` being definitionally equal, which should hold because both `toFun`s unfold to the same sum.

### [`P2MW.S_CerednikDrinfeld_natCard_ofFiniteIdele_primeHeckeSet_eq_natCard_subgroup_dualPair_ker_of_inf_conjByFiniteIdele.CerednikDrinfeld.LevelTransport.ker_comp_eq_sup_of_ker_eq_map`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_natCard_ofFiniteIdele_primeHeckeSet_eq_natCard_subgroup_dualPair_ker_of_inf_conjByFiniteIdele.lean#L1381-L1384) — `flt-anthropic-0515`

Snippet: `samples/flt-anthropic/flt-anthropic-0515.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddSubgroup.comap_map_eq
- **file**: Mathlib/Algebra/Group/Subgroup/Ker.lean
- **derivation**: by rw [← AddMonoidHom.comap_ker, hχ, AddSubgroup.comap_map_eq]
- **proof_uses_it**: True
- **explanation**: The theorem's mathematical content is Mathlib's `AddSubgroup.comap_map_eq` (additive form of `Subgroup.comap_map_eq`): `comap f (map f H) = H ⊔ f.ker`. The kernel of the composite, `(χ.comp φ).ker`, is by definition `χ.ker.comap φ`. Mathlib's `AddMonoidHom.comap_ker` states this and is proved by `rfl`. After that rewrite, substituting the hypothesis `hχ : χ.ker = H.map φ` gives exactly `comap φ (map φ H) = H ⊔ φ.ker`. So the theorem is `comap_map_eq` used with `χ.ker` in place of `map φ H`, and the only extra steps are definitional unfolding and a rewrite with the hypothesis. The library's current proof already does this, but it goes through its own wrapper `comap_map_eq_sup_ker` (line 1377), which is simply `AddSubgroup.comap_map_eq φ H`. Mathlib has no single lemma stated with the `hχ` hypothesis, so I classify this as a special case rather than a duplicate.

### [`P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite.hensSplit_isMaximal_map_mk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite.lean#L19-L26) — `flt-anthropic-0542`

Snippet: `samples/flt-anthropic/flt-anthropic-0542.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.IsMaximal.map_of_surjective_of_ker_le
- **file**: Mathlib/RingTheory/Ideal/Maps.lean
- **derivation**: by haveI := hm; exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hK)
- **explanation**: The Mathlib lemma is stated for any surjective ring hom `f` and any maximal ideal `m` (taken as an instance) with `RingHom.ker f ≤ m`. Its conclusion is `(m.map f).IsMaximal`. Take `f := Ideal.Quotient.mk K`: surjectivity is `Ideal.Quotient.mk_surjective`. The kernel condition becomes `K ≤ m` after rewriting with `Ideal.mk_ker` (a simp lemma), which is `hK`. Mathlib itself uses the lemma this way in `Mathlib/RingTheory/AdicCompletion/LocalRing.lean` (line 74). The library's proof works through `map_eq_top_or_isMaximal_of_surjective` plus its own comap/map helper, so it does not call this lemma.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional.KW47.ofReal_zpow_cpow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional.lean#L4601-L4612) — `flt-anthropic-0543`

Snippet: `samples/flt-anthropic/flt-anthropic-0543.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Complex.cpow_mul_ofReal_nonneg
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
- **derivation**: by simpa using (Complex.cpow_mul_ofReal_nonneg hq.le (j : ℝ) z).symm
- **explanation**: The Mathlib lemma states that for real x ≥ 0, real y and complex z, (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z, with x ^ y the real power. Taking x := q and y := (j : ℝ) and flipping the equation gives the theorem. The only glue is two simp lemmas: Real.rpow_intCast rewrites q ^ (j : ℝ) to the integer power q ^ j, and Complex.ofReal_intCast rewrites ((j : ℝ) : ℂ) to (j : ℂ). The library's proof does not use this lemma; it unfolds cpow through Complex.cpow_def_of_ne_zero and logarithms. Complex.cpow_int_mul was also checked and does not fit, because there the integer power is on the outside: x ^ (n * y) = (x ^ y) ^ n. The suggested derivation has not been compiled.

### [`P2MW.S_CerednikDrinfeld_germ_app_decomposition_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd.rdg_isIso_pullback_twist`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_germ_app_decomposition_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd.lean#L80-L93) — `flt-anthropic-0544`

Snippet: `samples/flt-anthropic/flt-anthropic-0544.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullback.map_isIso
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: haveI : IsIso e := ⟨⟨e', h1, h2⟩⟩
convert Limits.pullback.map_isIso f b f b (𝟙 _) e (𝟙 _) (by simp) (by simp [he]) using 2; simp
- **explanation**: Mathlib's `pullback.map_isIso` says that `pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ _ _` is an isomorphism whenever i₁, i₂ and i₃ are isomorphisms. Take g₁ = f₁ = f, g₂ = f₂ = b, i₁ = 𝟙 X, i₂ = e and i₃ = 𝟙 S. The hypotheses h1 and h2 give `IsIso e`, with e' as its inverse. Since `pullback.map` is an abbrev, this map unfolds to `pullback.lift (fst ≫ 𝟙 _) (snd ≫ e) _`. That differs from the theorem's lift only by `fst ≫ 𝟙 = fst`, which `convert`/`simp` takes care of. So the theorem is an instance of the Mathlib lemma, plus routine glue. The library instead builds the inverse by hand. I could not compile the derivation, so the exact `convert ... using 2` form may need small adjustments.

### [`P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.P2mKindSignCx.ridE_lamE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.lean#L85-L86) — `flt-anthropic-0555`

Snippet: `samples/flt-anthropic/flt-anthropic-0555.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.TensorProduct.rid_tmul
- **file**: Mathlib/RingTheory/TensorProduct/Maps.lean
- **derivation**: (Algebra.TensorProduct.rid_tmul (R := ℝ) ℝ (1 : ℝ) l).trans (one_smul ℝ l)
- **explanation**: `ridE` is the ring-equivalence form of Mathlib's `Algebra.TensorProduct.rid ℝ ℝ ℂ`, and `lamE l` is just `l ⊗ₜ 1`. So the theorem says `rid (l ⊗ₜ 1) = l`. Mathlib's `Algebra.TensorProduct.rid_tmul` says `rid R S A (a ⊗ₜ r) = r • a`, and it is proved by `rfl`. Taking `r = 1` and then applying `one_smul` gives the theorem. The library proof instead goes through its own lemma `ridE_tmul`, which is that same Mathlib fact repeated and proved by `rfl`, followed by `one_smul`. The suggested derivation has not been compiled, and it may need explicit `show`/unfolding of `ridE` and `lamE`. It should also be checked that the `leftAlgebra` instance elaborates to the instance `ridE` uses.

### [`P2MW.S_FreyPackage_frey_wild_inertia_at_two_trivial.FreyWild.one_lt_mul_self`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_wild_inertia_at_two_trivial.lean#L23-L24) — `flt-anthropic-0562`

Snippet: `samples/flt-anthropic/flt-anthropic-0562.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: one_lt_mul_self_iff
- **file**: Mathlib/Algebra/Order/Monoid/Defs.lean
- **derivation**: one_lt_mul_self_iff.mpr h
- **explanation**: This is a special case of Mathlib's `one_lt_mul_self_iff`. That lemma states `1 < a * a ↔ 1 < a` for any `[CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]`. A `LinearOrderedCommGroupWithZero` provides these instances, so the `.mpr` direction is exactly this theorem. Another one-line proof is `one_lt_mul'' h h` (`one_lt_mul''` is an alias of `Left.one_lt_mul'`, which assumes `[MulLeftMono α]`), taking `b := a`. The library's current proof uses neither lemma: it chains `lt_trans` with `lt_mul_self` from the `GroupWithZero` order lemmas.

### [`P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.isFinitePlace_placeOfEquation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.lean#L191-L193) — `flt-anthropic-0576`

Snippet: `samples/flt-anthropic/flt-anthropic-0576.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsDedekindDomain.HeightOneSpectrum.valuation_le_one
- **file**: Mathlib/RingTheory/DedekindDomain/AdicValuation.lean
- **derivation**: fun r => (heightOneSpectrumOfEquation h).valuation_le_one r
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `HeightOneSpectrum.valuation_le_one`, and the current proof already applies that lemma. The library's definitions just repackage it:
- `IsFinitePlace v` means `∀ r : W.CoordinateRing, algebraMap r ∈ v.toValuationSubring`.
- `placeOfEquation h` is `Place.ofHeightOneSpectrum (heightOneSpectrumOfEquation h)`.
- Its valuation subring is `(w.valuation F).valuationSubring`.

So once the definitions are unfolded, membership means exactly `(heightOneSpectrumOfEquation h).valuation W.FunctionField (algebraMap r) ≤ 1`. This is Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`, `v.valuation K r ≤ 1` for `r : R`, with `v` set to the specific height-one prime `heightOneSpectrumOfEquation h`. The real mathematical content, that elements of a Dedekind domain have valuation ≤ 1 at every height-one prime, is Mathlib's. The only work left is unfolding the library's definitions.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SesAffine.app_naturality`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.lean#L37-L42) — `flt-anthropic-0578`

Snippet: `samples/flt-anthropic/flt-anthropic-0578.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PresheafOfModules.naturality_apply
- **file**: Mathlib/Algebra/Category/ModuleCat/Presheaf.lean
- **derivation**: (PresheafOfModules.naturality_apply φ.val i.op m).symm
- **explanation**: `PresheafOfModules.naturality_apply (f : M₁ ⟶ M₂) (g : X ⟶ Y) (x : M₁.obj X) : Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x)` is the elementwise naturality of a morphism of presheaves of modules. Mathlib's `Scheme.Modules` API (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean) defines `Hom.app φ U := (forget₂ _ _).map (φ.val.app (.op U))` and `M.presheaf := M.1.presheaf`. With these definitions the theorem is that lemma applied to `f := φ.val`, `g := i.op`, `x := m`, with the two sides swapped; the two statements match only up to definitional unfolding. I could not run Lean, so I have not checked that `exact (…).symm` accepts this by defeq. If it does not, a `simpa`/`dsimp [Hom.app]` step should close the gap. The library's proof does the same thing by hand: it takes `PresheafOfModules.Hom.naturality`, applies `congr_fun`, and simplifies, which is exactly how Mathlib proves `naturality_apply`. Mathlib's `Scheme.Modules` API has no `Hom.app` naturality lemma of its own. One caveat: this is essentially a structural naturality fact, so it is borderline under the "general principles" exclusion. I count it because the matching lemma is a specific Mathlib declaration about Mathlib's own definitions, not about the library's.

### [`P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents.CycGenRepBody.coeff_hU`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents.lean#L106-L123) — `flt-anthropic-0591`

Snippet: `samples/flt-anthropic/flt-anthropic-0591.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Polynomial.coeff_freeMonic
- **file**: Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean
- **derivation**: Polynomial.coeff_freeMonic B d n
- **explanation**: The library's `hU B d := X ^ d + ∑ i : Fin d, C (MvPolynomial.X i) * X ^ (i : ℕ)` in `(MvPolynomial (Fin d) B)[X]` is the same term as Mathlib's `Polynomial.freeMonic R n := .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : ℕ)`, so the two are definitionally equal. `Polynomial.coeff_freeMonic` states `(freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0`, which is `coeff_hU` up to variable names and unfolding `hU`. The library proves it by hand with the same argument Mathlib uses (`Finset.sum_eq_single` / `Finset.sum_eq_zero`) instead of citing the lemma. The one-line derivation was not compiled.

### [`P2MW.S_AlgebraicCurve_finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.ToricBoundWire.Tate.one_tmul_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean#L71-L80) — `flt-anthropic-0593`

Snippet: `samples/flt-anthropic/flt-anthropic-0593.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.Flat.tensorProduct_mk_injective
- **file**: Mathlib/RingTheory/Flat/Basic.lean
- **derivation**: Module.Flat.tensorProduct_mk_injective ℤ_[p] ℚ_[p] (TateModule p M)
- **explanation**: Not compiled. Mathlib's `Module.Flat.tensorProduct_mk_injective R S M [FaithfulSMul R S] [Flat R M] : Injective (TensorProduct.mk R S M 1)` says the map `y ↦ 1 ⊗ₜ y` is injective. The theorem is the case R = ℤ_[p], S = ℚ_[p], M = TateModule p M. The hypotheses should come from instances: FaithfulSMul ℤ_[p] ℚ_[p] from the IsFractionRing instance; Flat from the scoped NoZeroSMulDivisors instance → Module.IsTorsionFree over a domain (NoZeroSMulDivisors/Defs.lean:56) → Flat over a Dedekind domain (Flat/TorsionFree.lean:143), with ℤ_[p] a DVR, hence a PID, hence Dedekind. Fallback: IsLocalizedModule.injective_iff_isRegular applied to the library's toRational map. The current proof argues by hand via IsLocalizedModule.eq_zero_iff.

### [`P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle.KcFinDim.restrictTo_univ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle.lean#L312-L314) — `flt-anthropic-0612`

Snippet: `samples/flt-anthropic/flt-anthropic-0612.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.piecewise_univ
- **file**: Mathlib/Data/Finset/Piecewise.lean
- **derivation**: Finset.piecewise_univ κ 1
- **explanation**: This is a special case of Mathlib's `Finset.piecewise_univ`, with `g := 1`. The library defines `restrictTo S κ := fun w => if w ∈ S then κ w else 1`. This matches Mathlib's `Finset.piecewise` definition (`fun i ↦ if i ∈ s then f i else g i`) exactly when `f := κ` and `g := 1`, since `(1 : ∀ w, K w) w` reduces to `1`. So `restrictTo S κ` and `S.piecewise κ 1` are equal by unfolding definitions. `Finset.piecewise_univ (f g : ∀ i, π i) : univ.piecewise f g = f` with `g := 1` then gives `restrictTo univ κ = κ`.

I have not compiled this. The one-line term should typecheck because the two sides unfold to the same thing; if `exact` does not accept it directly, `by unfold restrictTo; exact Finset.piecewise_univ κ 1` should work. The library's current proof uses `funext` and `simp` instead.

This verdict is borderline. The content is trivial, and the match depends on noticing that `restrictTo` is just `Finset.piecewise` with `1` as the default value.

### [`P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.PDivOrthCR.ev_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.lean#L119-L121) — `flt-anthropic-0626`

Snippet: `samples/flt-anthropic/flt-anthropic-0626.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.TensorProduct.lift_tmul
- **file**: Mathlib/RingTheory/TensorProduct/Maps.lean
- **derivation**: Algebra.TensorProduct.lift_tmul _ _ _ c x
- **proof_uses_it**: True
- **explanation**: The library defines `ev p w φ z := Algebra.TensorProduct.lift φ z (fun _ _ => Commute.all _ _)`. Mathlib's `Algebra.TensorProduct.lift_tmul` states `lift f g hfg (a ⊗ₜ b) = f a * g b`. Take f := φ and g := z, with hfg the commutativity proof that holds automatically in the commutative ring L. After `ev` is unfolded, `ev_tmul` is exactly that instance of `lift_tmul`. The current proof already applies `lift_tmul` directly, which works because `ev` unfolds by definition.

### [`P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.FALT.val_mapGL'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.lean#L266-L268) — `flt-anthropic-0637`

Snippet: `samples/flt-anthropic/flt-anthropic-0637.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.SpecialLinearGroup.mapGL_coe_matrix
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: Matrix.SpecialLinearGroup.mapGL_coe_matrix γ
- **explanation**: The Mathlib lemma `mapGL_coe_matrix (g : SpecialLinearGroup n R) : ((mapGL S g) : Matrix n n S) = g.map (algebraMap R S)` holds for any commutative ring `R` and any `R`-algebra `S`. Taking `n := Fin 2`, `R := ℤ` and `S := ℝ` gives exactly this theorem. Here `g.map` is `Matrix.map` applied to the coercion of `g` to a matrix. Both statements are proved by `rfl`, and the library's proof does not cite the Mathlib lemma.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap.B24D.isLocalizedModule_ιB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap.lean#L128-L132) — `flt-anthropic-0651`

Snippet: `samples/flt-anthropic/flt-anthropic-0651.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsLocalizedModule.rTensor
- **file**: Mathlib/RingTheory/Localization/BaseChange.lean
- **derivation**: have h : ιB (𝒪 := 𝒪) A N = TensorProduct.AlgebraTensorModule.rTensor 𝒪 _ (Algebra.linearMap B A) := by ext; rfl
h ▸ IsLocalizedModule.rTensor S (Algebra.linearMap B A)
- **explanation**: Mathlib's instance `IsLocalizedModule.rTensor` states that for an A-linear map `g : M →ₗ[A] M'` with `[IsLocalizedModule S g]`, the map `AlgebraTensorModule.rTensor R N g` is also a localization at S (S⁻¹M ⊗ N = S⁻¹(M ⊗ N)). The library's `latticeBaseChange 𝒪 K B N` is an abbreviation for `B ⊗[𝒪] ↥N.1`, and `ιB A N` is `LinearMap.rTensor` of the algebra map B → A, rebundled as a B-linear map. So `ιB A N` is the same map as `AlgebraTensorModule.rTensor 𝒪 ↥N.1 (Algebra.linearMap B A)`. Instantiate with A := B, M := B, M' := A, R := 𝒪, N := ↥N.1 and g := Algebra.linearMap B A. Mathlib already provides the instance `IsLocalizedModule S (Algebra.linearMap B A)` from `[IsLocalization S A]` (Algebra/Module/LocalizedModule/IsLocalization.lean). What remains is only the extensional identification of ιB with rTensor. The library's proof instead goes through `isLocalizedModule_iff_isBaseChange` with `IsBaseChange.of_equiv` and `cancelBaseChange`. The derivation was not compiled; if `ext; rfl` fails, `ext; simp [ιB_apply]` should close the identification.

### [`P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.PDivINJK.htf_K`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.lean#L246-L252) — `flt-anthropic-0676`

Snippet: `samples/flt-anthropic/flt-anthropic-0676.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: eq_zero_of_ne_zero_of_mul_left_eq_zero
- **file**: Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean
- **derivation**: eq_zero_of_ne_zero_of_mul_left_eq_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hx
- **explanation**: The Mathlib lemma `eq_zero_of_ne_zero_of_mul_left_eq_zero` says: in a ring with no zero divisors, `x ≠ 0` and `x * y = 0` give `y = 0`. The theorem is this lemma with `x := (p : OK p K)`. `OK p K` is a subalgebra of the field `PadicAlgCl p`, so Mathlib gives it no zero divisors (via the subring instances) and characteristic zero (via `SubsemiringClass.instCharZero`). The side condition `(p : OK p K) ≠ 0` is therefore `Nat.cast_ne_zero.mpr hp.ne_zero`. The library's proof does the same by hand: it maps to `PadicAlgCl p`, uses `mul_eq_zero` and `Subtype.ext`, and never calls this lemma. The derivation was not compiled; it assumes instance search finds both instances on `OK p K`.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_mem_closure_gluedPic0_mk_configuredPair.WSwapGenH.inv_efib_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_mem_closure_gluedPic0_mk_configuredPair.lean#L39-L43) — `flt-anthropic-0679`

Snippet: `samples/flt-anthropic/flt-anthropic-0679.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.hom_inv_apply
- **file**: Mathlib/AlgebraicGeometry/Scheme.lean
- **derivation**: haveI := 𝔛.efib_iso A hA ρ hρ
exact Scheme.hom_inv_apply (asIso (𝔛.efib A hA ρ hρ)) P
- **explanation**: Mathlib's `Scheme.hom_inv_apply (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x` says that the inverse of a scheme isomorphism undoes it on points. For schemes, applying a morphism to a point is defined as applying its `.base`. The library's theorem is this lemma with `e := asIso (𝔛.efib A hA ρ hρ)`, where the `IsIso` instance comes from `efib_iso`. Two definitional equalities make it match: `(asIso f).hom` is `f` and `(asIso f).inv` is `inv f`. Nothing in the statement depends on the library's particular map; it holds for any isomorphism of schemes. The current proof proves it directly with `Scheme.Hom.comp_apply` and `IsIso.hom_inv_id` instead of citing this lemma. I could not run Lean, so the derivation has not been compiled. It relies on those definitional equalities; if `exact` fails to unify, `simpa using` should work in its place.

### [`P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.LiNormSq.dens_slash`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean#L607-L612) — `flt-anthropic-0684`

Snippet: `samples/flt-anthropic/flt-anthropic-0684.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UpperHalfPlane.petersson_slash
- **file**: Mathlib/NumberTheory/ModularForms/Petersson.lean
- **derivation**: have h := UpperHalfPlane.petersson_slash k F F β x
rw [UpperHalfPlane.σ, if_pos hβ, abs_of_pos hβ, petersson_self_eq_dens, petersson_self_eq_dens] at h; simp only [ContinuousAlgEquiv.refl_apply] at h; exact_mod_cast h
- **proof_uses_it**: True
- **explanation**: This is a borderline call. Mathlib's `petersson_slash` states `petersson k (f ∣[k] g) (f' ∣[k] g) τ = |g.det.val| ^ (k - 2) * σ g (petersson k f f' (g • τ))`. The library's theorem takes f = f' = F and assumes `0 < det β`. With that assumption, σ β is the identity (`if_pos`) and the absolute value disappears (`abs_of_pos`). The result is then written with the library's own real-valued `dens k F x = ‖F x‖^2 * im x ^ k` instead of the complex value `petersson k F F x`. All of the mathematical content (how the slash action transforms the Petersson density) comes from `petersson_slash`, and the current proof already uses it. The glue is not purely routine, though: it rewrites with the library's own lemma `petersson_self_eq_dens` (proved from `Complex.conj_mul'`) and then removes casts. So it can also be read as a restatement through a library definition, which would make `none_found` defensible.

### [`P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm.R1G1COT.cusp_holo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm.lean#L610-L611) — `flt-anthropic-0687`

Snippet: `samples/flt-anthropic/flt-anthropic-0687.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CuspForm.holo'
- **file**: Mathlib/NumberTheory/ModularForms/Basic.lean
- **derivation**: F.holo'
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `CuspForm.holo'`. That declaration is the holomorphy field of the `CuspForm` structure: for any `Γ : Subgroup (GL (Fin 2) ℝ)`, every `f : CuspForm Γ k` satisfies `MDiff (f : ℍ → ℂ)`, and `MDiff` is notation for `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`. The library's theorem is that statement with `Γ` set to `Γ₁ℝ M`, the image of `Gamma1 M` in `GL (Fin 2) ℝ`. The coercions agree by definition, and the library's proof is literally `F.holo'`. The general form for any `CuspFormClass` is `CuspFormClass.holo`, so `CuspFormClass.holo F` would also prove it. The holomorphy is part of Mathlib's definition of a cusp form; none of it comes from the library's own definitions. The match could arguably be called `duplicate` instead, since Mathlib's statement is general in `Γ`; I chose `special_case` because the theorem fixes `Γ` to a specific subgroup.

### [`P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen.Ws47.PIN.Parity.centralScalar_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen.lean#L2073-L2077) — `flt-anthropic-0695`

Snippet: `samples/flt-anthropic/flt-anthropic-0695.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.scalar_commute
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: (Matrix.GeneralLinearGroup.scalar_commute zz g).symm
- **explanation**: This is a special case of a Mathlib lemma. In the library, `AdelicGL2 R K` is an abbrev for `Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)`, and `centralScalar R K` is defined as `Matrix.GeneralLinearGroup.scalar (Fin 2)`. Mathlib's `Matrix.GeneralLinearGroup.scalar_commute (u : Rˣ) (A : GL n R) : scalar n u * A = A * scalar n u` holds over any commutative ring `R`. Taking `n = Fin 2` and `R = AdeleRing (𝓞 ℚ) ℚ`, and unfolding `centralScalar`, gives the theorem with the two sides of the equation swapped, so `.symm` finishes it. The current proof does not use this lemma. It goes down to the underlying matrices and applies the matrix-level `Matrix.scalar_commute`. The derivation is untested: I could not run Lean. It relies on `centralScalar` (a plain `def`) unfolding definitionally when the term is elaborated; if it does not, `unfold centralScalar` first.

### [`P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.AnnulusG1.le_map_sum_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.lean#L265-L276) — `flt-anthropic-0699`

Snippet: `samples/flt-anthropic/flt-anthropic-0699.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddValuation.map_le_sum
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: tsub_le_iff_right.mp (v.map_le_sum fun k hk => tsub_le_iff_right.mpr (h k hk))
- **explanation**: `AddValuation.map_le_sum` says that if `g ≤ v (f i)` for every `i ∈ s`, then `g ≤ v (∑ i ∈ s, f i)`. The library theorem is this statement with a constant `w` added on the right of each inequality. In `ℕ∞`, which has `OrderedSub`, `n ≤ x + w` is equivalent to `n - w ≤ x` by `tsub_le_iff_right`. So the theorem is `map_le_sum` with `g := n - w`, plus `tsub_le_iff_right` to rewrite the hypotheses and the conclusion. The library's proof does not use this lemma: it redoes the Finset induction by hand with `v.map_add`.

### [`P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries.isNoetherianRing_fin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean#L242-L248) — `flt-anthropic-0710`

Snippet: `samples/flt-anthropic/flt-anthropic-0710.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPowerSeries.isNoetherianRing
- **file**: Mathlib/RingTheory/MvPowerSeries/Equiv.lean
- **derivation**: _root_.MvPowerSeries.isNoetherianRing R (σ := Fin n)
- **explanation**: The theorem is a special case of the Mathlib instance `MvPowerSeries.isNoetherianRing (S : Type*) [CommRing S] [IsNoetherianRing S] {σ} [Finite σ] : IsNoetherianRing (MvPowerSeries σ S)`, with σ := Fin n; the `Finite (Fin n)` instance is found automatically, so `inferInstance` should also work. Mathlib proves that instance from a private lemma `isNoetherianRing_fin` (same file, line 217). That lemma has the same statement and nearly the same proof as the library's theorem, but private declarations can't be cited. The library's proof does not use the instance: it inducts on n with `isEmptyRingEquiv`, `finSuccRingEquiv` and `isNoetherianRing_of_ringEquiv`, just as the private lemma does.

### [`P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.R1FrickeInt.mem_conj_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean#L193-L196) — `flt-anthropic-0724`

Snippet: `samples/flt-anthropic/flt-anthropic-0724.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.mem_inv_pointwise_smul_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Pointwise.lean
- **derivation**: by rw [ConjAct.toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
- **explanation**: This is a borderline call. Mathlib has `Subgroup.mem_inv_pointwise_smul_iff : x ∈ a⁻¹ • S ↔ a • x ∈ S`. Take `a = ConjAct.toConjAct g` and `S = Γ`. Then two simp-style rewrites finish the job: `ConjAct.toConjAct_inv` turns `toConjAct g⁻¹` into `(toConjAct g)⁻¹`, and `ConjAct.toConjAct_smul` unfolds the conjugation action to `g * x * g⁻¹`. Mathlib uses exactly this rewrite chain inline, for example in `NumberTheory/ModularForms/CongruenceSubgroups.lean` (around lines 206 and 213) and in `SlashInvariantForms.lean` (line 286). I searched for a dedicated lemma stating membership in a `ConjAct`-conjugated subgroup and found none. The library's current proof gets there through the sibling lemma `Subgroup.mem_pointwise_smul_iff_inv_smul_mem` plus `inv_inv`, not through `mem_inv_pointwise_smul_iff`. The cited lemma is a generic fact about pointwise actions, so this could also be judged `none_found`. I chose `special_case` because the only remaining step is unfolding the `ConjAct` definitions.

### [`P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.PMDND.norm_iteratedFDeriv_dir_le`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.lean#L211-L225) — `flt-anthropic-0727`

Snippet: `samples/flt-anthropic/flt-anthropic-0727.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: norm_iteratedFDeriv_clm_apply_const
- **file**: Mathlib/Analysis/Calculus/ContDiff/Bounds.lean
- **derivation**: simpa [dir, norm_iteratedFDeriv_fderiv] using norm_iteratedFDeriv_clm_apply_const (c := w) (n := j)
  ((contDiff_infty_iff_fderiv.1 hV).2.contDiffAt (x := p)) (by exact_mod_cast le_top)
- **explanation**: The library defines `dir w V = fun p => fderiv ℝ V p w`. Mathlib's `norm_iteratedFDeriv_clm_apply_const` says that `‖iteratedFDeriv 𝕜 n (fun y => f y c) x‖ ≤ ‖c‖ * ‖iteratedFDeriv 𝕜 n f x‖` whenever `f : E → F →L[𝕜] G` is `ContDiffAt 𝕜 N f x` with `n ≤ N`.

Take `f := fderiv ℝ V` and `c := w`. The smoothness hypothesis comes from `contDiff_infty_iff_fderiv`, which the library's proof already uses. This gives `‖iteratedFDeriv ℝ j (dir w V) p‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) p‖`. The rewrite lemma `norm_iteratedFDeriv_fderiv` (`‖iteratedFDeriv n (fderiv f) x‖ = ‖iteratedFDeriv (n+1) f x‖`) then turns the right-hand side into exactly the theorem's bound.

The library proof instead re-derives the bound by hand, using `iteratedFDeriv_comp_left` and an operator-norm estimate on `ContinuousLinearMap.apply`. I could not run Lean, so the two-line derivation above has not been compiled.

### [`P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.W769.coe_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean#L175-L176) — `flt-anthropic-0729`

Snippet: `samples/flt-anthropic/flt-anthropic-0729.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.coe_algebraMap_apply
- **file**: Mathlib/FieldTheory/IntermediateField/Basic.lean
- **derivation**: IntermediateField.coe_algebraMap_apply _ r
- **explanation**: The library's `qExpFunctionFieldC K Γ` is defined as an `IntermediateField K (LaurentSeries K)` (an `IntermediateField.adjoin`). Mathlib's `IntermediateField.coe_algebraMap_apply (S : IntermediateField K L) (x : K) : ↑(algebraMap K S x) = algebraMap K L x` says that for any intermediate field S, the coercion of `algebraMap K S x` into L equals `algebraMap K L x`. The theorem is this lemma with L taken to be `LaurentSeries K` and S taken to be `qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)`. That is why the verdict is special_case and not duplicate. The library proves it by `rfl`, and the Mathlib lemma is also proved by `rfl`, but the library proof does not cite the lemma.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit.mem_imS_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.lean#L50-L57) — `flt-anthropic-0746`

Snippet: `samples/flt-anthropic/flt-anthropic-0746.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Subring.mem_map_equiv
- **file**: Mathlib/Algebra/Ring/Subring/Basic.lean
- **derivation**: by unfold imS; exact Subring.mem_map_equiv
- **explanation**: This is a duplicate of `Subring.mem_map_equiv`. The library defines `imS e O := O.map e.toRingHom`, and Mathlib's lemma states `x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K` for any ring equivalence `f : R ≃+* S`. Once `imS` is unfolded, the two statements are the same. The coercion `(f : R →+* S)` and `e.toRingHom` should be definitionally equal (I expect so, but haven't checked it by compiling). Mathlib only needs rings, which is weaker than the fields assumed here, so the lemma applies in this setting as is. The current proof doesn't use the lemma: it goes through `Subring.mem_map` and `symm_apply_apply` by hand.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.S12EL.Int.den_eq_one_of_eq_intCast`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.lean#L115-L116) — `flt-anthropic-0753`

Snippet: `samples/flt-anthropic/flt-anthropic-0753.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Rat.den_intCast
- **file**: Init/Data/Rat/Lemmas.lean
- **derivation**: by rw [h]; exact Rat.den_intCast m
- **proof_uses_it**: True
- **explanation**: This is a special case of `Rat.den_intCast`, which is in Lean core (`Init/Data/Rat/Lemmas.lean`) and states `((a : ℤ) : ℚ).den = 1`. The theorem says the same thing for any `x` with `x = ↑m`: rewrite with the hypothesis `h`, then apply the lemma at `m`. The current proof already does exactly this. I also checked `Rat.den_eq_one_iff` in Mathlib's `Data/Rat/Defs.lean`, which states `r.den = 1 ↔ ↑r.num = r`. It is a different statement, and I did not find any Mathlib lemma that takes a hypothesis `x = ↑m` and concludes `x.den = 1`.

### [`P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero.P2MG3b.mem_span_X_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero.lean#L117-L119) — `flt-anthropic-0761`

Snippet: `samples/flt-anthropic/flt-anthropic-0761.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PowerSeries.X_dvd_iff
- **file**: Mathlib/RingTheory/PowerSeries/Basic.lean
- **derivation**: by rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
- **proof_uses_it**: True
- **explanation**: `PowerSeries.X_dvd_iff` states `X ∣ φ ↔ constantCoeff φ = 0` for any power series `φ` over a commutative semiring, which covers the theorem's commutative-ring setting. The theorem says the same thing with `X ∣ f` rewritten as `f ∈ Ideal.span {X}`. The general lemma `Ideal.mem_span_singleton` does that translation in one `rw`, and the library's own proof is exactly these two rewrites. So all the mathematical content comes from `X_dvd_iff`. I chose `special_case` over `duplicate` because the span-membership form is a reformulation that takes one extra rewrite, not just a change of notation; no argument needs to be instantiated. I found no Mathlib lemma for power series stated directly in span or kernel form, such as a `ker_constantCoeff` (that lemma exists only for polynomials and Witt vectors), or a `mem_span_X`.

### [`P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand.K9D.exp_neg_le_factorial_mul_inv_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand.lean#L75-L84) — `flt-anthropic-0764`

Snippet: `samples/flt-anthropic/flt-anthropic-0764.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.pow_div_factorial_le_exp
- **file**: Mathlib/Analysis/Complex/Exponential.lean
- **derivation**: rw [Real.exp_neg, ← div_eq_mul_inv, ← inv_div]
exact inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp x hx.le k)
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. `Real.pow_div_factorial_le_exp (hx : 0 ≤ x) (n : ℕ) : x ^ n / n ! ≤ exp x` carries all of the theorem's mathematical content. The theorem's goal, `exp (-x) ≤ k! * (x^k)⁻¹`, is just that inequality with both sides inverted:
- `exp (-x) = (exp x)⁻¹`, by `Real.exp_neg`;
- `k! * (x^k)⁻¹ = k! / x^k = (x^k / k!)⁻¹`, by `div_eq_mul_inv` and `inv_div`.

Inversion reverses the inequality because `x^k / k! > 0`. The library's own proof already uses `Real.pow_div_factorial_le_exp` and then rearranges by hand over several lines. The two-line derivation above does the same thing with rewrites plus `inv_anti₀`; I have not compiled it. I found no Mathlib lemma stating the `exp (-x)` form directly. I searched for `exp_neg_le…`, `factorial_mul_inv_pow`, and `exp (-…)` appearing together with `factorial`.

### [`P2MW.S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.R1AF8D2b.exists_sub_of_mem_map`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.lean#L693-L733) — `flt-anthropic-0770`

Snippet: `samples/flt-anthropic/flt-anthropic-0770.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AdicCompletion.ker_evalOneₐ_eq_map
- **file**: Mathlib/RingTheory/AdicCompletion/Completeness.lean
- **derivation**: obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
exact ⟨a, by rw [← AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I)]; simp [RingHom.mem_ker, ha]⟩
- **explanation**: For a finitely generated ideal I, Mathlib's `AdicCompletion.ker_evalOneₐ_eq_map` says that the kernel of `evalOneₐ I : AdicCompletion I R → R ⧸ I` is `I.map (algebraMap R (AdicCompletion I R))`. The theorem follows: since A is Noetherian, I is finitely generated. Lift `evalOneₐ I x` to some `a : A` (quotient maps are surjective). Then `x - of I A a` maps to zero under `evalOneₐ` (by `map_sub` and `evalOneₐ_of`), so it lies in the kernel, which is `I.map algebraMap`. The derivation was not compiled; the `simp` step may need an extra rewrite to match the coercion `(a : A ⧸ I)` with `Ideal.Quotient.mk I a`. The surjectivity of the quotient map is counted as routine glue, which is a judgment call. The library's proof does not use this lemma: it re-derives the kernel description through exactness of `AdicCompletion.map` and surjectivity of `ofTensorProduct`.

### [`P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt.FlatK1LC.det_apply_baseChangeAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt.lean#L43-L48) — `flt-anthropic-0771`

Snippet: `samples/flt-anthropic/flt-anthropic-0771.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.det_baseChange
- **file**: Mathlib/LinearAlgebra/Charpoly/BaseChange.lean
- **derivation**: letI : Algebra A B := φ.toAlgebra
exact LinearMap.det_baseChange (ρ.ρ σ)
- **proof_uses_it**: True
- **explanation**: I found a match in Mathlib: `LinearMap.det_baseChange`. It states that `LinearMap.det (f.baseChange A) = algebraMap R A (LinearMap.det f)` for an endomorphism `f` of a finite free module.

The library's `GaloisRepAdic.baseChangeAlong φ hφ ρ` is defined using the algebra structure `φ.toAlgebra`. It takes the module `B ⊗[A] ρ.V`, with each `σ` acting by `(ρ.ρ σ).baseChange B`. So, after unfolding the definition, the theorem is the Mathlib lemma with `R := A`, `A := B` and `f := ρ.ρ σ`, where `algebraMap A B = φ` holds by definition. The library's current proof does this unfolding with `show` and then applies `LinearMap.det_baseChange` directly. The theorem therefore adds nothing beyond this instantiation, which is why I classed it as a special case rather than an exact duplicate.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.Qc_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L203-L205) — `flt-anthropic-0773`

Snippet: `samples/flt-anthropic/flt-anthropic-0773.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_eq_zero_iff
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: by rw [Qc, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective]
   exact ModularForm.qExpansion_eq_zero_iff one_pos (by simp [Γ1]) F
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `ModularForm.qExpansion_eq_zero_iff`. The library's `Qc F` is just a thin wrapper, defined as `HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)`. The Mathlib lemma `ModularForm.qExpansion_eq_zero_iff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) : qExpansion h f = 0 ↔ f = 0` states that a modular form is zero exactly when its q-expansion is zero, which is the content of the theorem. Here it is instantiated with h = 1 and Γ = Γ1 N, where the membership side goal is closed by `simp`. The only other step is routine glue: unfold `Qc`, then rewrite with `map_eq_zero_iff` using `HahnSeries.ofPowerSeries_injective`, because an injective ring map sends only 0 to 0. The library's current proof already does exactly this.

### [`P2MW.S_LocalGL2_iwasawa_decomposition_diag.LocalGL2.exists_ratio_or_ratio`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalGL2_iwasawa_decomposition_diag.lean#L57-L74) — `flt-anthropic-0776`

Snippet: `samples/flt-anthropic/flt-anthropic-0776.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValuationRing.le_total
- **file**: Mathlib/RingTheory/Valuation/ValuationRing.lean
- **derivation**: (ValuationRing.le_total R K (Quotient.mk'' x : ValuationRing.ValueGroup R K) (Quotient.mk'' y)).imp
  (fun ⟨c, h⟩ => ⟨c, by rw [← h, Algebra.smul_def]⟩) fun ⟨c, h⟩ => ⟨c, by rw [← h, Algebra.smul_def]⟩
- **explanation**: I'm classing this as a special case of `ValuationRing.le_total`, not an exact duplicate. In Mathlib, `ValueGroup R K` is the quotient of `K` by the action of the units of `R`. The order on it is defined so that `⟦a⟧ ≤ ⟦b⟧` unfolds by definition to `∃ c : R, c • b = a`. `ValuationRing.le_total` states `a ≤ b ∨ b ≤ a` in `ValueGroup A K`, assuming `[ValuationRing A] [IsFractionRing A K]`.

Taking `a = ⟦x⟧` and `b = ⟦y⟧` gives `(∃ c, c • y = x) ∨ (∃ c, c • x = y)`. Rewriting with `Algebra.smul_def` turns this into the theorem's statement.

The `ValuationRing R` instance should come from the DVR assumption: a DVR is a local PID, so it is Bézout, and the instance at line 388 makes a local Bézout domain a `ValuationRing`.

Mathlib's proof of `le_total` is essentially the same argument as the library's: `div_surjective`, then the divisibility dichotomy, then `linear_combination`.

Two caveats:
- I could not run Lean, so the two-line derivation is untested. It relies on the quotient order unfolding by definition when the hypotheses are destructured.
- Mathlib's statement is about quotient classes in `ValueGroup R K`, not elements of `K` directly. That is why I chose `special_case` over `duplicate`.

### [`P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.FrickeSpan.mdifferentiable_disc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean#L52-L52) — `flt-anthropic-0777`

Snippet: `samples/flt-anthropic/flt-anthropic-0777.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CuspForm.holo'
- **file**: Mathlib/NumberTheory/ModularForms/Basic.lean
- **derivation**: CuspForm.discriminant.holo'
- **proof_uses_it**: True
- **explanation**: The theorem is a special case: it follows directly from Mathlib's structure field `CuspForm.holo'`, applied to the specific cusp form `CuspForm.discriminant`. The library's proof already does exactly this.

- `CuspForm.holo'` (line 84 of Basic.lean) states `MDiff (toSlashInvariantForm : ℍ → ℂ)`, i.e. that every cusp form is holomorphic as a function ℍ → ℂ.
- `CuspForm.discriminant : CuspForm 𝒮ℒ 12` is defined in Mathlib/NumberTheory/ModularForms/Discriminant.lean (line 237). Its `holo'` field is proved there from the differentiability of η.
- Its coercion to a function is `ModularForm.discriminant` by `rfl` (`coe_discriminant`).

So the theorem's statement is exactly that field for Δ. The class version `CuspFormClass.holo CuspForm.discriminant` would also work.

The mathematical content (Δ is holomorphic) is proved inside Mathlib's own definition, not in the library. However, I found no standalone Mathlib lemma such as `mdifferentiable_discriminant`. I grepped for MDifferentiable/holo in Discriminant.lean, the Eta file and Basic.lean, and only the structure field matched.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.P2mWs11RBC.op_hom_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.lean#L18-L19) — `flt-anthropic-0778`

Snippet: `samples/flt-anthropic/flt-anthropic-0778.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.subsingleton_of_unop
- **file**: Mathlib/CategoryTheory/Opposites.lean
- **derivation**: Subsingleton.elim i j
- **explanation**: This is a special case of the Mathlib instance `CategoryTheory.subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B)`, which says that morphisms in an opposite category form a subsingleton whenever the morphisms in the other direction of the original category do. Its hypothesis is supplied by the instance `CategoryTheory.Preorder.subsingleton_hom` in `Mathlib/CategoryTheory/Category/Preorder.lean`, which applies here because `Y.Opens` is a preorder. Taking C = Y.Opens, A = op U and B = op V, `Subsingleton (op U ⟶ op V)` is found automatically, so `Subsingleton.elim i j` proves the theorem directly. The library's current proof instead uses `Quiver.Hom.unop_inj` to go back to `V ⟶ U` and applies the preorder subsingleton fact there; it never goes through the opposite-category instance.

### [`P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central.LTMiddleIdentity.mC_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central.lean#L73-L73) — `flt-anthropic-0783`

Snippet: `samples/flt-anthropic/flt-anthropic-0783.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: NNReal.coe_nonneg
- **file**: Mathlib/Data/NNReal/Defs.lean
- **derivation**: NNReal.coe_nonneg _
- **explanation**: The library's `LanglandsTunnell.TateLocal.modulus` (Definitions/Def_LanglandsTunnell_TateLocalZeta.lean) takes values in `ℝ≥0`. So the theorem says that an `ℝ≥0` value, cast to `ℝ`, is nonnegative. That is Mathlib's `NNReal.coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r` with `r := modulus (x : K)`. The library's proof instead weakens the strict positivity lemma `mC_pos`. This is a trivial instance: all the content comes from the codomain type, not from the library's own definition. Whether it should count as `special_case` or fall under the generic-lemma exclusion is a judgement call.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow.H34A.pmap_some`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow.lean#L53-L57) — `flt-anthropic-0789`

Snippet: `samples/flt-anthropic/flt-anthropic-0789.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Affine.Point.map_some
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
- **derivation**: WeierstrassCurve.Affine.Point.map_some (Algebra.ofId K F) h
- **explanation**: This is a special case of Mathlib's `Point.map_some`. The library's `pmap W` is defined as `WeierstrassCurve.Affine.Point.baseChange (W' := W) K F`. In Mathlib, `baseChange` is an `abbrev` for `map (Algebra.ofId K F)`. `Point.map_some` says `map f (some _ _ h) = some _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h)`, which is proved by `rfl`. Taking R = S = K, the original field F := K, the target field K := F and f := Algebra.ofId K F gives the library's statement. The point coordinates `f x` and `algebraMap K F x` agree definitionally. The two nonsingularity proofs (`map_nonsingular` vs `baseChange_nonsingular`) are equal by proof irrelevance. The library proves its lemma by `rfl` instead of citing `map_some`. I have not compiled the suggested term; if elaboration needs help, `rfl` or `(map_some ..).trans rfl` should also work.

### [`P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi.WsB.L2H.max20`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi.lean#L36-L36) — `flt-anthropic-0803`

Snippet: `samples/flt-anthropic/flt-anthropic-0803.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: max_eq_left
- **file**: Mathlib/Order/Defs/LinearOrder.lean
- **derivation**: max_eq_left (Fin.zero_le _)
- **explanation**: `max_eq_left` states `b ≤ a → max a b = a` in any linear order. `@[to_dual]` generates it from `min_eq_left` at line 192 of `Mathlib/Order/Defs/LinearOrder.lean`. The theorem is the case `a = (2 : Fin 3)`, `b = 0`. The side condition `0 ≤ 2` is supplied by core's `Fin.zero_le`. The library proves the statement by `decide` instead. It is only a concrete numeric fact, so this is a trivial special case.

### [`P2MW.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.TwPT.algebraMap_withAbs_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.lean#L71-L73) — `flt-anthropic-0806`

Snippet: `samples/flt-anthropic/flt-anthropic-0806.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WithAbs.ofAbs_algebraMap
- **file**: Mathlib/Analysis/Normed/Ring/WithAbs.lean
- **derivation**: WithAbs.ofAbs_injective w.1 (by simpa using WithAbs.ofAbs_algebraMap v.1 w.1 x)
- **explanation**: I'm counting this as a special case of `WithAbs.ofAbs_algebraMap`, though it's a borderline call. The library proves the theorem with `rfl`: it just unfolds Mathlib's `WithAbs.algebraLeft` instance, and the `LiesOver` hypothesis isn't used.

Mathlib's lemma says `(algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs` for any absolute values `v` on `R` and `w` on `T`. Setting `R = K`, `T = L`, `v = v.1`, `w = w.1` gives the library's statement, up to the definitional identities `WithAbs.equiv v x = x.ofAbs` and `(WithAbs.equiv w).symm y = toAbs w y` (from `equiv`'s `@[simps]` lemmas). Going from that to the equation in `WithAbs w.1` takes injectivity of `ofAbs`, or structure eta. So the two say the same thing, just with or without `ofAbs` applied to both sides.

I haven't compiled the derivation. The `simpa` step is only there to turn `equiv`/`equiv.symm` back into `ofAbs`/`toAbs`. Since everything is definitional, `rfl` (the current proof) also works.

Another route is `WithAbs.algebraMap_left_apply` followed by `WithAbs.algebraMap_right_apply`, which expands the same instance in two steps.

### [`P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.R4GC.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.lean#L1522-L1523) — `flt-anthropic-0815`

Snippet: `samples/flt-anthropic/flt-anthropic-0815.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.C_eq_algebraMap
- **file**: Mathlib/RingTheory/HahnSeries/Multiplication.lean
- **derivation**: RingHom.congr_fun HahnSeries.C_eq_algebraMap c
- **explanation**: Mathlib has `HahnSeries.C_eq_algebraMap : C = algebraMap R R⟦Γ⟧`, which is proved by `rfl`. `LaurentSeries L` is an abbrev for `L⟦ℤ⟧`, i.e. `HahnSeries ℤ L`. So the library theorem is this equality of ring homomorphisms with Γ := ℤ and R := L, applied to the element `c`. The only glue is `RingHom.congr_fun`; `rfl` should also work. The library's proof does not use this lemma. It rewrites with `algebraMap_laurentSeries_eq_single` and `HahnSeries.C_apply` instead.

### [`P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.CartierExistenceIntSol.incl_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.lean#L421-L424) — `flt-anthropic-0826`

Snippet: `samples/flt-anthropic/flt-anthropic-0826.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.map_injective
- **file**: Mathlib/Algebra/MvPolynomial/Eval.lean
- **derivation**: fun P Q h => MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) (by simpa only [incl_apply] using h)
- **proof_uses_it**: True
- **explanation**: The library defines `incl p` as `MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])`, which `incl_apply` rewrites to `MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])`. Mathlib's `MvPolynomial.map_injective` says that if `f` is injective, then `MvPolynomial.map f` is injective. Instantiating it with `f = algebraMap ℤ_[p] ℚ_[p]` and `σ = Fin 2 × ℕ` gives the theorem. The injectivity hypothesis is supplied by `IsFractionRing.injective ℤ_[p] ℚ_[p]`. Supplying it from a second standard lemma is borderline as routine glue, but the derivation is still one line with no further argument. The current proof does exactly this: it rewrites with `incl_apply` and applies `map_injective`.

### [`ModularCurve.uvSwapEquiv_C`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_UVCrossingModel.lean#L64-L66) — `flt-anthropic-0829`

Snippet: `samples/flt-anthropic/flt-anthropic-0829.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPowerSeries.rename_C
- **file**: Mathlib/RingTheory/MvPowerSeries/Rename.lean
- **derivation**: MvPowerSeries.rename_C (⇑(Equiv.swap (0 : Fin 2) 1)) w
- **proof_uses_it**: True
- **explanation**: This is a special case of `MvPowerSeries.rename_C`. The library defines `uvSwapEquiv` as `(MvPowerSeries.renameEquiv W (Equiv.swap 0 1)).toRingEquiv`, and `uvSwapEquiv_apply` shows by `rfl` that applying it is the same as applying `MvPowerSeries.rename (Equiv.swap 0 1)`. Mathlib's `MvPowerSeries.rename_C` says `rename f (C r) = C r` for any map `f`. Taking `f = Equiv.swap (0 : Fin 2) 1` and `r = w` gives the theorem once the library's thin wrapper is unfolded; that unfolding is definitional, so the one-line term above should typecheck. The current proof already uses this lemma, as `rw [uvSwapEquiv_apply, MvPowerSeries.rename_C]`.

### [`P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.K1aOfFinite.det_globalPoints`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.lean#L37-L42) — `flt-anthropic-0832`

Snippet: `samples/flt-anthropic/flt-anthropic-0832.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.map_det
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: by unfold globalPoints; exact Matrix.GeneralLinearGroup.map_det (algebraMap F 𝔸) γ
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Matrix.GeneralLinearGroup.map_det`. In the library, `globalPoints` is defined as `Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))`. Mathlib's lemma states `det (map f g) = Units.map f (det g)` for any ring hom `f`. Unfolding `globalPoints` and taking `f := algebraMap F 𝔸` gives the theorem. The only gap is coercion: the theorem writes `(algebraMap F 𝔸).toMonoidHom` where Mathlib uses the coercion of `f` to a monoid hom, and the two agree definitionally. The current proof already uses this lemma: it unfolds, rewrites with `map_det`, and closes with `rfl`. I could not run Lean, so the one-line `exact` above is unchecked. If it fails on the coercion, the library's current `unfold; rw; rfl` proof is the fallback.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.CerednikDrinfeld.QM.SpecialOfFEC.lp_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.lean#L117-L118) — `flt-anthropic-0833`

Snippet: `samples/flt-anthropic/flt-anthropic-0833.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Commute.map
- **file**: Mathlib/Algebra/Group/Commute/Hom.lean
- **derivation**: ((Commute.all a a').map (lp X)).eq
- **explanation**: This is a borderline call. `lp X` is a ring hom `Zp2 q →+* Matrix (Fin 2) (Fin 2) B`, and `Zp2 q` is commutative. The theorem says the images of two elements commute, and the proof uses nothing about `lp` except that it is multiplicative. `Commute.map` (`Commute x y → Commute (f x) (f y)` for any `MulHomClass` map `f`) applied to `Commute.all a a'` (which is `mul_comm`) gives exactly this statement, and `.eq` unfolds `Commute`. The current proof gets the same result directly with `map_mul` and `mul_comm`. Under a strict reading of the exclusion for generic homomorphism laws, the answer could be none_found instead. I found no more specific Mathlib lemma about images of a hom from a commutative monoid commuting.

### [`P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot.W1TW.mneZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot.lean#L25-L25) — `flt-anthropic-0844`

Snippet: `samples/flt-anthropic/flt-anthropic-0844.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Int.natCast_ne_zero
- **file**: Init/Data/Int/LemmasAux.lean
- **derivation**: Int.natCast_ne_zero.mpr (NeZero.ne m)
- **explanation**: The theorem says that `(m : ℤ) ≠ 0` whenever `[NeZero m]`. Lean core's `Int.natCast_ne_zero {n : Nat} : (n : Int) ≠ 0 ↔ n ≠ 0` gives this when its `.mpr` direction is applied to `NeZero.ne m`. Two other routes work just as well. Mathlib's `Nat.cast_ne_zero` (Algebra/CharZero/Defs.lean) can be used with `R := ℤ`. The instance `NeZero.charZero` also provides `NeZero ((m : ℕ) : ℤ)` directly, so `NeZero.ne (m : ℤ)` closes the goal. The library's proof uses `exact_mod_cast`, which gets there through cast normalisation rather than by calling the lemma explicitly.

### [`P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.HeckeCartan.mem_integers_of_valued_le_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.lean#L123-L124) — `flt-anthropic-0848`

Snippet: `samples/flt-anthropic/flt-anthropic-0848.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
- **file**: Mathlib/RingTheory/DedekindDomain/AdicValuation.lean
- **derivation**: (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx
- **proof_uses_it**: True
- **explanation**: The match is `HeightOneSpectrum.mem_adicCompletionIntegers`, which I read in Mathlib/RingTheory/DedekindDomain/AdicValuation.lean. It says `x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1` for any Dedekind domain R with fraction field K. The library's theorem is the `.mpr` direction of that lemma with R := 𝓞 ℚ and K := ℚ. Because it fixes these arguments rather than restating the lemma in general, it is a special case, not a duplicate. The current proof already applies this exact lemma.

### [`ModularCurve.TatePoint.charZero_H`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_CycSubRootBridge.lean#L23-L24) — `flt-anthropic-0852`

Snippet: `samples/flt-anthropic/flt-anthropic-0852.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: algebraRat.charZero
- **file**: Mathlib/Algebra/CharP/Algebra.lean
- **derivation**: algebraRat.charZero H
- **explanation**: H is defined as `HahnSeries ℚ Qbar`, where Qbar := AlgebraicClosure ℚ. Mathlib's `algebraRat.charZero (R) [Nontrivial R] [Ring R] [Algebra ℚ R] : CharZero R` applies with R := H. H is a ring and is nontrivial because Qbar is. The `Algebra ℚ H` instance comes from Mathlib's HahnSeries algebra instance (`instance : Algebra R A⟦Γ⟧`), built from the ℚ-algebra structure of AlgebraicClosure ℚ. The library instead uses RingHom.charZero_iff with the injectivity of HahnSeries.C, carrying the property over from Qbar. Mathlib has no CharZero instance or lemma for HahnSeries itself in RingTheory/HahnSeries, so this is a special case rather than a duplicate. The one-line derivation was not compiled.

### [`P2MW.S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient.P2MKcStabDual.nsmul_ne_zero_of_mem_Icc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient.lean#L164-L166) — `flt-anthropic-0860`

Snippet: `samples/flt-anthropic/flt-anthropic-0860.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: nsmul_ne_zero_of_lt_addOrderOf
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
- **proof_uses_it**: True
- **explanation**: The Mathlib lemma is `nsmul_ne_zero_of_lt_addOrderOf`, the additive version that `to_additive` generates from `pow_ne_one_of_lt_orderOf` (line 249 of that file). It states that `n ≠ 0` and `n < addOrderOf x` give `n • x ≠ 0`, in any additive monoid. The library's theorem takes the group of points of a Weierstrass curve for that monoid. Its hypotheses are `addOrderOf Q = N`, `1 ≤ k` and `k ≤ N - 1`. These turn into Mathlib's hypotheses with `omega`, after rewriting `addOrderOf Q` to `N`. The library's proof already consists of exactly this one-line application.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt.CerednikDrinfeld.FormalOmega.LevelAux.red_zero_eq_id`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt.lean#L136-L140) — `flt-anthropic-0876`

Snippet: `samples/flt-anthropic/flt-anthropic-0876.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.factorₐ_refl
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: by unfold red; exact Ideal.Quotient.factorₐ_refl _
- **explanation**: The library defines `red π n` as `Ideal.Quotient.factorₐ 𝒪 (span_pow_le_span_one π n)`. That inclusion goes from `span {π^(n+1)}` to `span {π^(0+1)}`. When `n = 0` both ideals are the same, `span {algebraMap 𝒪 R π ^ (0+1)}`. By proof irrelevance, the inclusion proof is then definitionally `le_refl I`. Mathlib's `Ideal.Quotient.factorₐ_refl` says `Ideal.Quotient.factorₐ R (le_refl I) = AlgHom.id R _` for any ideal `I`. So the theorem is that lemma with `I` set to this particular ideal. The library proves it directly instead, using `Ideal.Quotient.algHom_ext`, `AlgHom.ext` and `rfl`. I have not run the derivation, but it should go through by `unfold red` followed by `exact Ideal.Quotient.factorₐ_refl _`.

### [`P2MW.S_AutomorphicForm_setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab.R4OrthSigma.regular_adelicGLHaar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab.lean#L136-L138) — `flt-anthropic-0878`

Snippet: `samples/flt-anthropic/flt-anthropic-0878.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.regular_haarMeasure
- **file**: Mathlib/MeasureTheory/Measure/Haar/Basic.lean
- **derivation**: by dsimp only [adelicGLHaar, Measure.haar]; exact Measure.regular_haarMeasure
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `regular_haarMeasure`. The library defines `adelicGLHaar (Fin 2) (𝓞 L) L` (Definitions/Def_NumberField_AdelicHaar.lean) as `Measure.haar` on `GL (Fin 2) (AdeleRing (𝓞 L) L)`, using the library's Borel structure `glBorel`. In Mathlib, `Measure.haar` is an `abbrev` for `haarMeasure K₀`, with `K₀` an arbitrarily chosen positive compact set. Mathlib's instance `regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).Regular` says the Haar measure is regular. Taking `G := GL₂(𝔸_L)` and that `K₀` gives exactly the theorem. The current proof already relies on it: it unfolds `adelicGLHaar` and `Measure.haar`, and `infer_instance` then finds this instance. The theorem adds nothing beyond unfolding the library's definition.

### [`P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.P2mResNorm.mem_span_pow_of_le`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.lean#L45-L48) — `flt-anthropic-0879`

Snippet: `samples/flt-anthropic/flt-anthropic-0879.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: pow_dvd_pow
- **file**: Mathlib/Algebra/Divisibility/Basic.lean
- **derivation**: Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hML) h
- **proof_uses_it**: True
- **explanation**: `Ideal.mem_span_singleton` rewrites membership in `Ideal.span {a}` as divisibility by `a`. After that, the theorem says that `p ^ L ∣ x` implies `p ^ M ∣ x` when `M ≤ L`. This is `pow_dvd_pow (p : ℤ_[p]) hML : p ^ M ∣ p ^ L` chained with `h`, so the theorem is `pow_dvd_pow` instantiated at `a := (p : ℤ_[p])` plus routine glue. The current proof already does this: it rewrites with `Ideal.mem_span_singleton` and then uses `(pow_dvd_pow _ hML).trans h`. An equivalent route goes through `Ideal.span_singleton_le_span_singleton` (`span {x} ≤ span {y} ↔ y ∣ x`), which gives the ideal inclusion directly. I found no Mathlib lemma stating the ideal-membership form itself. I searched for `span {x ^ n} ≤ span {x ^ m}`, `mem_span_singleton_pow` and `pow_dvd_of_le_of_pow_dvd`. Combining `Ideal.pow_le_pow_right` with `Ideal.span_singleton_pow` also works, but it uses two substantive lemmas. This is a judgement call: the mathematical content is exactly `pow_dvd_pow`, and only the translation between membership and divisibility is added. If that translation is not counted as glue, the verdict would be `none_found`.

### [`P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot.LinkLift.hom_eval`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot.lean#L28-L30) — `flt-anthropic-0882`

Snippet: `samples/flt-anthropic/flt-anthropic-0882.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Polynomial.eval_map_apply
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: (Polynomial.eval_map_apply χ a).symm
- **explanation**: Mathlib's `Polynomial.eval_map_apply` (with `[Semiring R] [Semiring S] (f : R →+* S) {p : R[X]} (x : R)`) states `(p.map f).eval (f x) = f (p.eval x)`. This is the library's statement `χ (p.eval a) = (p.map χ).eval (χ a)` with the sides swapped. Mathlib only needs `Semiring` where the library assumes `CommRing`, which is a weaker requirement. The library's proof does not use this lemma: it rewrites with `eval_map` and `eval₂_at_apply`, which are the two lemmas Mathlib's own proof of `eval_map_apply` combines.

### [`P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq.ModularCurve.ARails.coeff_prod_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_E4_mul_eta_pow_eight_eq.lean#L230-L238) — `flt-anthropic-0888`

Snippet: `samples/flt-anthropic/flt-anthropic-0888.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PowerSeries.coeff_mul_prod_one_sub_of_lt_order
- **file**: Mathlib/RingTheory/PowerSeries/Order.lean
- **derivation**: rw [← Finset.prod_sdiff hs, mul_comm]
exact PowerSeries.coeff_mul_prod_one_sub_of_lt_order _ _ _ _ fun i hi => by simp [PowerSeries.order_X_pow] at hi ⊢; norm_cast; omega
- **explanation**: This is a special case of `PowerSeries.coeff_mul_prod_one_sub_of_lt_order`. That lemma says: if `↑k < (f i).order` for every `i ∈ s`, then `coeff k (φ * ∏ i ∈ s, (1 - f i)) = coeff k φ`.

Instantiate it as follows:
- `k := m`;
- the index set is `s \ range (m+1)`;
- `φ := ∏ n ∈ range (m+1), (1 - X^(n+1))`;
- `f i := X^(i+1)`.

The library's proof begins with the same step: `Finset.prod_sdiff` followed by `mul_comm`. After that, the goal has exactly the form of the Mathlib lemma. The only side condition is `↑m < order (X^(i+1))` for `i ∉ range (m+1)`. Rewriting with `order_X_pow` turns it into `m < i+1`, which `norm_cast; omega` closes.

The library's current proof does not use this lemma. It goes through its own `coeff_mul_of_cong`, `Cong.prod` and `Cong.one_sub_X_pow` helpers instead. I have not compiled the suggested derivation.

I also considered `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` (the pentagonal number theorem file). It only says the coefficient is eventually constant and gives no explicit bound, so it does not give this statement directly.

### [`P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower.pow_q_eq_of_mem_k`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.lean#L683-L686) — `flt-anthropic-0900`

Snippet: `samples/flt-anthropic/flt-anthropic-0900.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiniteField.pow_card
- **file**: Mathlib/FieldTheory/Finite/Basic.lean
- **derivation**: haveI := Fintype.ofFinite k
rw [← hq, Nat.card_eq_fintype_card, FiniteField.pow_card]
- **proof_uses_it**: True
- **explanation**: This is a special case of `FiniteField.pow_card`, and the library's proof already uses that lemma. In a finite field `K` with `[Fintype K]`, the lemma says `a ^ Fintype.card K = a`. The theorem states the same fact with `Finite k` and a hypothesis `Nat.card k = p ^ n`. It is derived by:
- building a `Fintype` instance with `Fintype.ofFinite`;
- rewriting `p ^ n` back to `Nat.card k`, then `Nat.card` to `Fintype.card` with `Nat.card_eq_fintype_card`;
- applying `FiniteField.pow_card`.

It is not a duplicate in the strict sense, because the theorem is phrased with `Nat.card` and an explicit `p ^ n` rather than `Fintype.card`. I looked in Mathlib for a version stated with `Nat.card` or `Finite` and found none: `FiniteField.pow_card_pow` raises the exponent to `card ^ n` instead.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.U2Dual.norm_le_one_iff_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.lean#L182-L184) — `flt-anthropic-0902`

Snippet: `samples/flt-anthropic/flt-anthropic-0902.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valued.toNormedField.norm_le_one_iff
- **file**: Mathlib/Topology/Algebra/Valued/NormedValued.lean
- **derivation**: by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact Valued.toNormedField.norm_le_one_iff
- **explanation**: The norm on `p.adicCompletion ℚ` is Mathlib's `instNormedFieldValuedAdicCompletion`, defined as `Valued.toNormedField (adicCompletion K v) ℤᵐ⁰`, with rank-one structure `instRankOneAdicCompletion`. For any valued field `L` with value group `Γ₀` and a rank-one structure, `Valued.toNormedField.norm_le_one_iff` states `‖x‖ ≤ 1 ↔ val.v x ≤ 1`. Here `L` is `adicCompletion ℚ p` and `Γ₀` is `ℤᵐ⁰`. Membership `x ∈ adicCompletionIntegers ℚ p` unfolds to `Valued.v x ≤ 1`: `HeightOneSpectrum.mem_adicCompletionIntegers` proves this by `Iff.rfl`. So the theorem is that lemma with the right-hand side unfolded. The derivation above has not been compiled. The library proves it differently, by rewriting with its own `norm_le_norm_iff_v_le_v`, which goes through `FinitePlace.norm_def` and `toNNReal` strict monotonicity. `Valued.integer.mem_iff` was ruled out because it is stated for `NormedField.valuation`, not the `ℤᵐ⁰` valuation used here.

### [`P2MW.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.WindB.dotR_sub_right`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.lean#L1248-L1249) — `flt-anthropic-0909`

Snippet: `samples/flt-anthropic/flt-anthropic-0909.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: dotProduct_sub
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: dotProduct_sub ξ x x'
- **explanation**: The library defines `dotR ξ x := ∑ i, ξ i * x i`. This has exactly the same body as Mathlib's `dotProduct v w := ∑ i, v i * w i` (Mathlib/Data/Matrix/Mul.lean), so `dotR ξ x` is definitionally `ξ ⬝ᵥ x`. Mathlib's `dotProduct_sub (u v w : m → α) : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w` holds for any `NonUnitalNonAssocRing α` and `Fintype m`. Taking `α := ℝ` and `m := Fin r` gives the theorem. The derivation `dotProduct_sub ξ x x'` relies on Lean unfolding `dotR` to `dotProduct`; I could not run Lean to check this, but the two bodies are syntactically the same. The library's proof does not use this lemma: it unfolds `dotR` and finishes with `mul_sub` and `Finset.sum_sub_distrib`. Since `dotR` is just a renamed copy of `dotProduct`, the theorem's content is Mathlib's `dotProduct_sub`, instantiated to `ℝ` and `Fin r`.

### [`P2MW.S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic.WChartField.coeffEmb_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic.lean#L44-L49) — `flt-anthropic-0917`

Snippet: `samples/flt-anthropic/flt-anthropic-0917.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RingHom.injective
- **file**: Mathlib/RingTheory/SimpleRing/Basic.lean
- **derivation**: (coeffEmb L).injective
- **explanation**: `RingHom.injective {R S} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S] [Nontrivial S] (f : R →+* S) : Function.Injective f` says a ring hom out of a simple ring (for example a field) into a nontrivial ring is injective. `coeffEmb L : LaurentSeries ℚ →+* LaurentSeries L` is a ring hom whose domain is a field (Mathlib's `HahnSeries.instField`) and whose codomain is nontrivial, so the theorem is `RingHom.injective` applied to `f := coeffEmb L`. Mathlib uses `f.injective` the same way for ring homs between fields, e.g. in `rangeRestrictField_bijective`. The library's proof instead compares coefficients and uses that `algebraMap ℚ L` is injective. Mathlib has no HahnSeries.map-injectivity lemma; the corresponding lemmas exist only for power series, polynomials and Witt vectors. The derivation was not compiled.

### [`P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq.ModularCurve.ARails.Cong.one_sub_X_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_E4_mul_eta_pow_eight_eq.lean#L219-L221) — `flt-anthropic-0927`

Snippet: `samples/flt-anthropic/flt-anthropic-0927.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: pow_dvd_pow
- **file**: Mathlib/Algebra/Divisibility/Basic.lean
- **derivation**: by rw [Cong, sub_sub_cancel_left, dvd_neg]; exact pow_dvd_pow _ hn
- **proof_uses_it**: True
- **explanation**: This is a special case of `pow_dvd_pow`, which says `a ^ m ∣ a ^ n` whenever `m ≤ n`. In the library, `Cong m G` is defined as `X ^ (m + 1) ∣ G - 1` for integer power series. So the goal unfolds to `X ^ (m + 1) ∣ (1 - X ^ (n + 1)) - 1`. Rewriting with `sub_sub_cancel_left` and `dvd_neg` turns this into `X ^ (m + 1) ∣ X ^ (n + 1)`, which is `pow_dvd_pow` with `a := PowerSeries.X` and `hn : m + 1 ≤ n + 1`. The only real content is that lemma; the definition is just unfolded and the rest is routine rewriting. The library's proof already does exactly this, in two lines.

### [`P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed.WeierstrassCurve.DrinfeldGlobal.UnivFormalAdd.constantCoeff_fgGenW`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed.lean#L161-L163) — `flt-anthropic-0928`

Snippet: `samples/flt-anthropic/flt-anthropic-0928.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PowerSeries.constantCoeff_subst_eq_zero
- **file**: Mathlib/RingTheory/PowerSeries/Substitution.lean
- **derivation**: PowerSeries.constantCoeff_subst_eq_zero hz _ W.constantCoeff_formalW
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma. The library defines `W.fgGenW z := PowerSeries.subst z W.formalW` (Definitions/Def_WeierstrassCurve_FormalGroup.lean). Mathlib's `PowerSeries.constantCoeff_subst_eq_zero (ha : a.constantCoeff = 0) (f : PowerSeries R) (hf : f.constantCoeff = 0) : MvPowerSeries.constantCoeff (subst a f) = 0` gives the theorem once we take `a := z` and `f := W.formalW`. The remaining hypothesis `hf` is the library's own lemma `W.constantCoeff_formalW`, which says `formalW` has constant coefficient zero. So the main content, that substitution keeps a zero constant coefficient, is in Mathlib, and the only fact about the library's definition is that side condition. This is a borderline call: a library lemma is not on the list of allowed routine glue, and one could argue the result is partly about the library's own definitions. The current proof is already exactly this one-line application of the Mathlib lemma.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul.PV6R1.opHom_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul.lean#L21-L22) — `flt-anthropic-0934`

Snippet: `samples/flt-anthropic/flt-anthropic-0934.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.subsingleton_of_unop
- **file**: Mathlib/CategoryTheory/Opposites.lean
- **derivation**: Subsingleton.elim f g
- **explanation**: The theorem says any two morphisms between the same two objects of `(Y.Opens)ᵒᵖ` are equal, i.e. the hom-type is a subsingleton. Mathlib states exactly this for any category as the instance `CategoryTheory.subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B)`. Take `C := Y.Opens`. The required instance `Subsingleton (unop B ⟶ unop A)` is supplied by `CategoryTheory.Preorder.subsingleton_hom`, since `Y.Opens` is a preorder. Instance resolution then finds `subsingleton_of_unop`, so `Subsingleton.elim f g` proves the statement directly. The library's proof does not use this instance. It drops to the underlying morphisms with `Quiver.Hom.unop_inj` and applies `Subsingleton.elim` to them there. Since the match requires fixing `C` to the opens of a scheme, this is a special case rather than a duplicate.

### [`P2MW.S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization.AutomorphicForm.TwistedBruhat.mulVec_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization.lean#L1703-L1711) — `flt-anthropic-0950`

Snippet: `samples/flt-anthropic/flt-anthropic-0950.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.mulVec_fin_two
- **file**: Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean
- **derivation**: by rw [Matrix.mulVec_fin_two, funext_iff, Fin.forall_fin_two]; simp
- **explanation**: I found no Mathlib lemma with this exact iff, but one Mathlib lemma does the real work. `Matrix.mulVec_fin_two` (for any semiring R) says that for a 2×2 matrix m and a vector v, `m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1]`. That is exactly the expansion the library theorem relies on. To get the theorem, rewrite with it, then use `funext_iff` and `Fin.forall_fin_two` to turn the vector equality into the two entry equations. A `simp` call then evaluates the `![..]` entries and `(c • w) i = c * w i`, which closes the goal. This is ordinary glue code, so the theorem is a special case of `Matrix.mulVec_fin_two` with R set to the field L. I have not compiled this derivation. The library's current proof unfolds `mulVec`/`dotProduct` by hand and does not use the Mathlib lemma.

### [`P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.residue_aeval_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean#L96-L102) — `flt-anthropic-0958`

Snippet: `samples/flt-anthropic/flt-anthropic-0958.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.map_aeval_eq_aeval_map
- **file**: Mathlib/Algebra/Polynomial/AlgebraMap.lean
- **derivation**: map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl G x
- **explanation**: The theorem is a special case of `Polynomial.map_aeval_eq_aeval_map`. That lemma states `ψ (aeval a p) = aeval (ψ a) (p.map φ)` for any ring homs `φ : R →+* T` and `ψ : S →+* U`, given the compatibility hypothesis `(algebraMap T U).comp φ = ψ.comp (algebraMap R S)`. Set `φ := residue A` and `ψ := residue B`. The compatibility square then holds by `rfl`, because the algebra map `ResidueField A → ResidueField B` comes from the `IsLocalHom` instance. Mathlib itself does exactly this in `Mathlib/RingTheory/LocalRing/Etale.lean`: `map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl p β`. The library's own proof does not cite this lemma; it argues directly with `eval₂_map` and `hom_eval₂`.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer.isClosedImmersion_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.lean#L29-L33) — `flt-anthropic-0959`

Snippet: `samples/flt-anthropic/flt-anthropic-0959.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.isClosedImmersion_of_comp_eq_id
- **file**: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
- **derivation**: isClosedImmersion_of_comp_eq_id f (L.one (𝟙 (Spec (CommRingCat.of K)))).1 (L.one _).2
- **explanation**: The theorem is a special case of `isClosedImmersion_of_comp_eq_id`, so I'm calling it `special_case`, not `duplicate`.

What the theorem says: `L.one (𝟙 _)` is a `SchemeHomOver`, i.e. a subtype `{φ : Spec K ⟶ A // φ ≫ f = 𝟙 _}`. So `.1` is a section `s` of `f` with `s ≫ f = 𝟙 (Spec K)`, and the claim is that `s` is a closed immersion.

The Mathlib lemma `isClosedImmersion_of_comp_eq_id {X Y} [Subsingleton Y] (f : X ⟶ Y) (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) : IsClosedImmersion g` says that any section of a morphism to a scheme with one point is a closed immersion. Taking `Y := Spec K` gives the theorem, and it doesn't need the `IsSeparated f` hypothesis at all. The required `Subsingleton (Spec (CommRingCat.of K))` instance is found automatically: Mathlib itself uses it the same way in `Mathlib/AlgebraicGeometry/Group/Abelian.lean`, with `Y := Spec (.of K)`.

The library's current proof takes a different route. It applies `AlgebraicGeometry.IsClosedImmersion.of_comp` (in `Morphisms/Separated.lean`: if `f ≫ g` is a closed immersion and `g` is separated, then `f` is a closed immersion), after first rewriting `s ≫ f` to `𝟙`. So it relies on the separatedness hypothesis rather than on `Spec K` having one point.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.R4RRN.mul_apply_10`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.lean#L172-L173) — `flt-anthropic-0964`

Snippet: `samples/flt-anthropic/flt-anthropic-0964.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.two_mul_expl
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by rw [Matrix.SpecialLinearGroup.coe_mul]; exact (Matrix.two_mul_expl _ _).2.2.1
- **explanation**: `Matrix.two_mul_expl` holds for any 2×2 matrices A, B over a `NonUnitalNonAssocSemiring R`. It is a conjunction of the four entry formulas for A * B; its third part is `(A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0`. The library theorem is that part with R = ℤ and A, B the underlying matrices of elements of SL(2, ℤ). Rewriting with `SpecialLinearGroup.coe_mul` turns the product into a matrix product, and the `.2.2.1` part of the lemma closes the goal. The library proof does not use this lemma: it expands with `Matrix.mul_apply` and `Fin.sum_univ_two` instead.

### [`P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector.ParchProof.inclArch_mulSingle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector.lean#L52-L54) — `flt-anthropic-0976`

Snippet: `samples/flt-anthropic/flt-anthropic-0976.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidHom.noncommPiCoprod_mulSingle
- **file**: Mathlib/GroupTheory/NoncommPiCoprod.lean
- **derivation**: MonoidHom.noncommPiCoprod_mulSingle _ w k
- **proof_uses_it**: True
- **explanation**: This is a special case of `MonoidHom.noncommPiCoprod_mulSingle`, and the library's proof already applies that lemma. The library defines `inclArch F := MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F) _`. The Mathlib lemma says that `noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y` for any family `ϕ` of pairwise-commuting monoid homs. Taking `ϕ := archRowIsometryInclAt₀ F` and unfolding `inclArch` gives exactly the theorem. Nothing about the specific maps is used, so the whole mathematical content comes from the Mathlib lemma.

### [`P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.NilYoneda.coeff_eq_zero_of_mem_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.lean#L331-L333) — `flt-anthropic-0986`

Snippet: `samples/flt-anthropic/flt-anthropic-0986.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.mem_pow_idealOfVars_iff'
- **file**: Mathlib/RingTheory/MvPolynomial/Ideal.lean
- **derivation**: (MvPolynomial.mem_pow_idealOfVars_iff' N p).mp hp d hd
- **explanation**: I found this in Mathlib. The library's `varIdeal R σ` is an abbrev for `Ideal.span (Set.range MvPolynomial.X)`. That is word for word the definition of Mathlib's abbrev `MvPolynomial.idealOfVars σ R`. Mathlib's `mem_pow_idealOfVars_iff'` states `p ∈ idealOfVars σ R ^ n ↔ ∀ x, degree x < n → p.coeff x = 0`. The theorem is the forward (`.mp`) direction of that iff, applied to `d` and `hd`. Mathlib needs no `Fintype` or `DecidableEq` assumptions, so it applies to the library's setting as is. Mathematically the two say the same thing. I answered special_case rather than duplicate only because it takes one direction of an iff, using `.mp` as glue. The library's current proof does not use this lemma: it goes through its own ideal `lowVanish` and proves `varIdeal_pow_le_lowVanish` by induction.


## Formal Frontier (46 flagged)

### [`CentralPolynomialSimplex.generator_mem_center`](https://github.com/FormalFrontier/simplicial-rings/blob/79a68e78417cb591897f5d8cfdb56c81334e365e/SimplicialRings/CentralPolynomialSimplex.lean#L60-L64) — `formal-frontier-0024`

Snippet: `samples/formal-frontier/formal-frontier-0024.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddMonoidAlgebra.of'_commute
- **file**: Mathlib/Algebra/MonoidAlgebra/Defs.lean
- **derivation**: Semigroup.mem_center_iff.mpr fun p =>
  (AddMonoidAlgebra.of'_commute (R := R) (M := Fin n →₀ ℕ) (fun _ => add_comm _ _) p).eq.symm
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of `AddMonoidAlgebra.of'_commute`, and the library's proof already applies it. That lemma says: if `∀ a', AddCommute a a'` holds, then `Commute (of' R M a) f` for every `f : AddMonoidAlgebra R M`. Here `generator n j` is by definition `of' R (Fin n →₀ ℕ) (Finsupp.single j 1)`. Since `Fin n →₀ ℕ` is additively commutative, `add_comm` discharges the hypothesis. Membership in `Set.center` is then routine glue: `Semigroup.mem_center_iff.mpr` turns it into commuting with every element, which the `Commute` fact gives via `.eq.symm`. So the result follows by instantiating the exponent monoid and the element `a := single j 1`. I found no Mathlib lemma that states center membership for `of'` or `single` directly in monoid algebras: grepping `center` in `Mathlib/Algebra/MonoidAlgebra` finds only docstring mentions in `Lift.lean`.

### [`SphereTopology.eastVector_norm`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Circle.lean#L54-L55) — `formal-frontier-0096`

Snippet: `samples/formal-frontier/formal-frontier-0096.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.norm_single
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: by simpa [eastVector] using PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) 0 (1 : ℝ)
- **proof_uses_it**: True
- **explanation**: In the library, `E2 := EuclideanSpace ℝ (Fin 2)` and `eastVector := PiLp.single 2 0 1`. Mathlib's `PiLp.norm_single (p) (β) (i) (b) : ‖single p i b‖ = ‖b‖` is a `@[simp]` lemma. With p = 2, β = fun _ => ℝ, i = 0 and b = 1, it gives `‖eastVector‖ = ‖(1 : ℝ)‖`, and `norm_one` reduces the right side to 1. So the theorem is a concrete instance of `PiLp.norm_single`. The library's proof, `simp [eastVector]`, most likely goes through this lemma: it is tagged simp and matches the unfolded goal directly. I did not run Lean to check which lemmas simp actually uses.

### [`CategoryTheory.CartesianMonoidalCategory.tensorLeftIsoProd_hom_app_fst`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/SingleCoverGroup.lean#L58-L63) — `formal-frontier-0146`

Snippet: `samples/formal-frontier/formal-frontier-0146.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
- **file**: Mathlib/CategoryTheory/Limits/IsLimit.lean
- **derivation**: (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.left⟩
- **proof_uses_it**: True
- **explanation**: This is a special case of a Mathlib lemma, and the library's proof already applies that lemma directly. Mathlib defines `tensorLeftIsoProd X` in Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean. Its component at `Y` is `(tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso (limit.isLimit _)`. Mathlib does not state a projection lemma for this isomorphism. So I found no direct duplicate, and grepping Mathlib for `tensorLeftIsoProd` turns up only the definition and one use.

The general lemma `IsLimit.conePointUniqueUpToIso_hom_comp` says `(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.app j`. Take P = `tensorProductIsBinaryProduct A B`, Q = `limit.isLimit (pair A B)` and j = `⟨.left⟩`. After unfolding `tensorLeftIsoProd`, its `.hom.app B` is exactly the iso in that lemma, `t.π.app ⟨.left⟩` is `prod.fst`, and `s.π.app ⟨.left⟩` is `fst A B`. That is the theorem's statement, and the library proves it with this one-line term.

### [`PrimeMultiplicity.awayValuation_mk'`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/PrimeMultiplicity.lean#L164-L170) — `formal-frontier-0155`

Snippet: `samples/formal-frontier/formal-frontier-0155.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valuation.extendToLocalization_mk'
- **file**: Mathlib/RingTheory/Valuation/ExtendToLocalization.lean
- **derivation**: by unfold awayValuation localizationValuation; rw [Valuation.extendToLocalization_mk']
- **explanation**: This is a special case of Mathlib's `Valuation.extendToLocalization_mk'`. In the library, `awayValuation hp` is defined as `localizationValuation hp (powers_le_nonZeroDivisors hp)`, which in turn is defined as `(valuation hp).extendToLocalization (S := S) …`. So `awayValuation` is just Mathlib's `Valuation.extendToLocalization`, with `v := valuation hp` and `S := Submonoid.powers p`. The Mathlib lemma says `(v.extendToLocalization hS B) (IsLocalization.mk' _ x y) = v x * (v y)⁻¹` for any valuation `v`, submonoid `S` and element `y : S`. With those choices of `v` and `S`, this is exactly the theorem.

The library's own definitions only wrap the extension; the mathematical content of the formula is Mathlib's. The current proof calls the library lemma `localizationValuation_mk'`, which is itself a one-line `rw` with the Mathlib lemma. So the current proof relies on the Mathlib lemma only indirectly, which is why `proof_uses_it` is false.

### [`ModuleCat.FiniteProjective.rankModuleFinite`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Module/LocallyConstantRank.lean#L324-L331) — `formal-frontier-0161`

Snippet: `samples/formal-frontier/formal-frontier-0161.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.Finite.pi
- **file**: Mathlib/RingTheory/Finiteness/Basic.lean
- **derivation**: haveI (i : Fin (rankBound f)) : Module.Finite R (Ideal.span {rankIdempotent f i}) := Module.Finite.span_singleton R _
exact Module.Finite.pi
- **explanation**: `rankModule R f` is a reducible abbreviation for the Pi type `(i : Fin (rankBound f)) → Ideal.span {rankIdempotent f i}`. Mathlib's instance `Module.Finite.pi` says a product of finitely many finite modules over a finite index type is finite. Here the index type is `Fin (rankBound f)`, and each factor is a principal ideal, which is finite by the instance `Module.Finite.span_singleton`. That instance has to be supplied by hand only because `Ideal.span` does not unfold to `Submodule.span` during instance search. So the theorem is `Module.Finite.pi` applied to this family, plus routine instance glue; none of its content depends on the library's definitions. The library's current proof takes a detour instead: it goes through `DirectSum.linearEquivFunOnFintype` and `Module.Finite.equiv`, and does not apply `Module.Finite.pi`. I checked both Mathlib statements in the sources but could not compile the suggested two-line derivation.

### [`Profinite.exists_stageHomClass`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteTargetHomColimit.lean#L197-L205) — `formal-frontier-0236`

Snippet: `samples/formal-frontier/formal-frontier-0236.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Profinite.exists_hom
- **file**: Mathlib/Topology/Category/Profinite/Extend.lean
- **derivation**: obtain ⟨i, g, rfl⟩ := exists_hom c hc f
exact ⟨i, g, colimit.ι_desc_apply (stageHomCocone c S) (Opposite.op i) g⟩
- **proof_uses_it**: True
- **explanation**: The theorem is Mathlib's `Profinite.exists_hom` restated through the library's own wrappers. Mathlib's lemma has the same setting (a cofiltered `I`, `F : I ⥤ FintypeCat.{max u w}`, a limit cone `c` of `F ⋙ toProfinite`, and a map `f : c.pt ⟶ toProfinite.obj X`). It gives `∃ i g, f = c.π.app i ≫ toProfinite.map g`. In the library, `stageHomToContinuous c S` is `colimit.desc` of a cocone whose component at `i` sends `g` to `c.π.app i ≫ toProfinite.map g`, and `stageHomClass F S i g` is `colimit.ι … (op i) g`. Unfolding these with the generic `colimit.ι_desc_apply` (this is what the library's `stageHomToContinuous_class` says) gives exactly Mathlib's equation with the two sides swapped. All the mathematical content is in `exists_hom`; the rest just unfolds definitions. The current proof already applies `exists_hom` and then that library lemma. It is classed as a special case rather than a duplicate only because the statement has to be unfolded first.

### [`MonoidAlgebra.liftGroupLikeBialgHom_mapDomain_comp`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Bialgebra/MonoidAlgebra.lean#L192-L203) — `formal-frontier-0240`

Snippet: `samples/formal-frontier/formal-frontier-0240.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.mapDomainBialgHom_comp
- **file**: Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean
- **derivation**: by rw [mapDomainBialgHom_comp, BialgHom.comp_assoc]
- **explanation**: This is a special case of Mathlib's `MonoidAlgebra.mapDomainBialgHom_comp`, which says `mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g)`. Use it with `f : M →* GroupLike R A` and `g := α`, then post-compose both sides with `liftGroupLikeBialgHom`, which is also defined in Mathlib. After rewriting with it, the two sides differ only by bracketing, and `BialgHom.comp_assoc` closes the goal. So all the theorem says beyond the Mathlib lemma is that composition can be rebracketed. The library proves it differently, by checking both sides on basis elements with `liftGroupLikeBialgHom_mapDomain_eq_iff` and `mapDomainBialgHom_single`. I could not run Lean, so the one-line `rw` derivation has not been compiled.

### [`QuadraticAlgebra.definingPolynomial_monic`](https://github.com/FormalFrontier/quadratic-algebras/blob/85a6b1bc79989b524a4ecdae6cce17b712a7bd2d/QuadraticAlgebras/AdjoinRoot.lean#L46-L49) — `formal-frontier-0245`

Snippet: `samples/formal-frontier/formal-frontier-0245.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.monic_X_pow_sub
- **file**: Mathlib/Algebra/Polynomial/Monic.lean
- **derivation**: monic_X_pow_sub degree_linear_lt
- **proof_uses_it**: True
- **explanation**: The library defines `definingPolynomial a b` as `X ^ 2 - (C b * X + C a)`. Mathlib's `Polynomial.monic_X_pow_sub` says `degree p < n → Monic (X ^ n - p)`. Taking `n := 2` and `p := C b * X + C a` gives the theorem. The side condition `degree (C b * X + C a) < 2` is exactly Mathlib's `Polynomial.degree_linear_lt`, a basic degree fact. The library's proof is already this one-liner. I found no Mathlib lemma stated directly for monic quadratics.

### [`ContinuousCohomology.CorestrictionTransversal.changeRep_rightCoset`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/Corestriction.lean#L168-L174) — `formal-frontier-0260`

Snippet: `samples/formal-frontier/formal-frontier-0260.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.IsComplement.rightCosetEquivalence_equiv_snd
- **file**: Mathlib/GroupTheory/Complement.lean
- **derivation**: Eq.symm (S.2.rightCosetEquivalence_equiv_snd (t : G))
- **explanation**: The library defines `changeRep T S t := (S.2.equiv (t : G)).2`, where `S.2 : IsComplement (H : Set G) S`. Unfolding this, the theorem says `RightCosetEquivalence H ((S.2.equiv t).2 : G) t`. Mathlib's `IsComplement.rightCosetEquivalence_equiv_snd (g : G) : RightCosetEquivalence H g ((hHT.equiv g).snd : G)` states the same thing with the two sides the other way round, for an arbitrary `g`. `RightCosetEquivalence s a b` is defined as `op a • s = op b • s`, so `Eq.symm` reverses it. To get the library's theorem, take `hHT := S.2` and `g := (t : G)`. The library's current proof does not cite this lemma: it unfolds to `rightCoset_eq_iff` and uses `changeFactor_mul_changeRep`. I have not compiled the suggested derivation. If `Eq.symm` does not see through the definition, `(rightCosetEquivalence_rel _).symm (...)` does the same job.

### [`Algebra.GrothendieckAddGroup.lift_of`](https://github.com/FormalFrontier/group-theory/blob/2b14628cb53e79783bd51baadcb4fc85667c8da3/GroupTheory/MonoidLocalization/GrothendieckGroup.lean#L43-L46) — `formal-frontier-0274`

Snippet: `samples/formal-frontier/formal-frontier-0274.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddSubmonoid.LocalizationMap.lift_eq
- **file**: Mathlib/GroupTheory/MonoidLocalization/Maps.lean
- **derivation**: AddSubmonoid.LocalizationMap.lift_eq (addMonoidOf ⊤) (fun _ ↦ AddGroup.isAddUnit _) a
- **explanation**: In Mathlib, `Algebra.GrothendieckAddGroup.lift f` is defined as `(addMonoidOf ⊤).lift (g := f) (fun _ ↦ AddGroup.isAddUnit _)`, and `of` is `(addMonoidOf ⊤).toAddMonoidHom`; both come from the `@[to_additive]` versions of `GrothendieckGroup.lift` and `GrothendieckGroup.of`. Once `lift` is unfolded, the statement `lift f (of a) = f a` is `AddSubmonoid.LocalizationMap.lift_eq` (`f.lift hg (f x) = g x`, the additive version of `Submonoid.LocalizationMap.lift_eq`) with the localization map set to `addMonoidOf ⊤`. Mathlib's Grothendieck group file has no `lift_of` lemma of its own; it only has `lift_symm_apply` (from simps) and `lift_apply`. The library's proof goes a different way, using the general fact `Equiv.symm_apply_apply` together with the definitional form of `lift.symm`. The suggested one-line derivation depends on `exact` seeing through the coercion of the `Equiv` `lift` by definitional unfolding. I could not run Lean, so this derivation has not been compiled.

### [`AlgebraicGeometry.SheafedSpace.restrictOnPreimage_unique`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/NativeOpenRestriction.lean#L66-L77) — `formal-frontier-0288`

Snippet: `samples/formal-frontier/formal-frontier-0288.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq
- **file**: Mathlib/Geometry/RingedSpace/OpenImmersion.lean
- **derivation**: InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_uniq _ _ (restrictOnPreimage_range g V) _ (congrArg (fun m => m.hom) comm))
- **proof_uses_it**: True
- **explanation**: This is a borderline call. The library defines `restrictOnPreimage g V` as `InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift f g' H)`, where `f` is the underlying presheafed-space map of `Y.ofRestrict V.isOpenEmbedding` and `g'` is the underlying map of the composite `X.ofRestrict _ ≫ g`. Mathlib's `PresheafedSpace.IsOpenImmersion.lift_uniq (H) (l) (hl : l ≫ f = g) : l = lift f g H` is exactly the uniqueness half of the universal property of this lift. The theorem is that lemma with `f` and `g` set to these two restriction maps. The only extra steps are moving from SheafedSpace morphisms to PresheafedSpace morphisms with `InducedCategory.hom_ext` and `congrArg (·.hom)`, plus the library's range lemma for the side condition. The library's proof already applies `lift_uniq` directly. Mathlib has no `SheafedSpace.IsOpenImmersion.lift` (only PresheafedSpace and LocallyRingedSpace versions), so there is no closer match. The one-line derivation given has not been compiled. It should work because `restrictOnPreimage` is `@[expose]` and should unfold by definitional equality, but if that fails, the current proof's `unfold restrictOnPreimage; dsimp` would be needed. One could instead answer `none_found`, on the grounds that the result is mainly a fact about the library's own definition. I chose `special_case` because the mathematical content is entirely Mathlib's uniqueness of the open-immersion lift.

### [`AlgebraicGeometry.Scheme.Hom.kernImage_mono`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/KernImage.lean#L62-L64) — `formal-frontier-0301`

Snippet: `samples/formal-frontier/formal-frontier-0301.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.kernImage_mono
- **file**: Mathlib/Data/Set/Lattice/Image.lean
- **derivation**: fun _ _ h ↦ Set.kernImage_mono h
- **proof_uses_it**: True
- **explanation**: The library's `π.kernImage hπ W` is just `Set.kernImage π W` packaged as a `B.Opens`, and the order on opens is inclusion of the underlying sets. So once the bundled definition is unfolded, the claim `Monotone (π.kernImage hπ)` is Mathlib's `Set.kernImage_mono : Monotone (kernImage f)` with `f` taken to be the underlying map of `π` and the arguments restricted to opens. The library's one-line proof already applies that lemma directly. The mathematical content is all in Mathlib. The library adds only the bundling into `Opens`, using `isClosedMap_iff_kernImage` for openness. I found no Mathlib declaration that already bundles `kernImage` as opens.

### [`RingedSpaces.Modules.RingedSpacePullback.nativeComparison_counit`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/RingedSpacePullback.lean#L195-L200) — `formal-frontier-0326`

Snippet: `samples/formal-frontier/formal-frontier-0326.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit
- **file**: Mathlib/CategoryTheory/Adjunction/Unique.lean
- **derivation**: Adjunction.leftAdjointUniq_hom_app_counit (adjunction f) (nativeAdjunction f) N
- **proof_uses_it**: True
- **explanation**: The library defines `nativeComparison f` as `(adjunction f).leftAdjointUniq (nativeAdjunction f)`, which is an instance of Mathlib's general construction. Mathlib's lemma says that for any two adjunctions `adj1 : F ⊣ G` and `adj2 : F' ⊣ G`, `(leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x`. Setting adj1 := adjunction f, adj2 := nativeAdjunction f, G := pushforwardFunctor f and x := N gives the theorem exactly, after unfolding the definition. The library's proof is already this one-line application. It is a special case rather than a duplicate because the general adjunctions have to be instantiated with the library's specific ones.

### [`TopCat.isOpenCover_twoOpenCover`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/MayerVietoris.lean#L205-L212) — `formal-frontier-0338`

Snippet: `samples/formal-frontier/formal-frontier-0338.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: iSup_bool_eq
- **file**: Mathlib/Order/CompleteLattice/Lemmas.lean
- **derivation**: by rw [sup_comm] at hUV; simpa [IsOpenCover, iSup_bool_eq, twoOpenCover] using hUV
- **explanation**: `IsOpenCover u` is by definition `iSup u = ⊤`, and `twoOpenCover U V = fun b ↦ if b then V else U` is the library's own definition. So the theorem says only that `⨆ b : Bool, (if b then V else U) = ⊤` given `U ⊔ V = ⊤`. Mathlib's `iSup_bool_eq : ⨆ b : Bool, f b = f true ⊔ f false`, instantiated at `f := twoOpenCover U V`, gives `V ⊔ U`, which matches the hypothesis up to `sup_comm`. The current proof does not cite this lemma: it proves the same equality with `ext x` and `simp [twoOpenCover]`. This is borderline: apart from unfolding the library's definitions, the only content is this general lattice fact about suprema over `Bool`. Mathlib's `sup_eq_iSup` states the same fact with `cond`. The derivation was not compiled.

### [`ModuleCat.nonempty_iso_iff_finrank_eq`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Category/FiniteModuleDimension.lean#L56-L67) — `formal-frontier-0357`

Snippet: `samples/formal-frontier/formal-frontier-0357.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
- **file**: Mathlib/LinearAlgebra/Dimension/Free.lean
- **derivation**: ⟨fun ⟨e⟩ => ⟨e.toLinearEquiv⟩, fun ⟨e⟩ => ⟨e.toModuleIso⟩⟩.trans FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
- **explanation**: Mathlib's `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq` assumes a ring `R` with `StrongRankCondition` and modules `M`, `M'` that are free and finite. It states `Nonempty (M ≃ₗ[R] M') ↔ finrank R M = finrank R M'`. The library theorem is the same statement with `M`, `M'` taken to be the carriers of `X Y : ModuleCat R`, and with `Nonempty (X ≅ Y)` in place of `Nonempty (X ≃ₗ[R] Y)`. Passing between the two uses only routine glue that Mathlib already provides: `Iso.toLinearEquiv` and `LinearEquiv.toModuleIso`, together with the definitional equality `ModuleCat.of R X = X`, which the current proof already relies on. All the mathematical content is in the Mathlib lemma.

The library's proof does not use the iff itself. It rebuilds it from its two halves: `LinearEquiv.finrank_eq` and `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`, which is exactly how Mathlib proves `nonempty_linearEquiv_iff_finrank_eq`.

I found no `ModuleCat`-level version (a `Nonempty` iso stated in terms of `finrank`) in `Mathlib/Algebra/Category/ModuleCat`.

### [`CategoryTheory.MorphismProperty.Over.pullbackPairingSymmetry_hom_app_fst`](https://github.com/FormalFrontier/morphism-properties/blob/3c50b1e5fea23c3a119c5eb9157c3a1ba7f3b8bc/MorphismProperties/PullbackPairing.lean#L365-L373) — `formal-frontier-0372`

Snippet: `samples/formal-frontier/formal-frontier-0372.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: by rw [pullbackPairingSymmetry_hom_app_left]; exact pullbackSymmetry_hom_comp_fst A.hom B.hom
- **proof_uses_it**: True
- **explanation**: This is a borderline call. The library's `pullbackPairingSymmetry` is a natural isomorphism. Its `.left` component at `(A, B)` is, by definition, Mathlib's `(pullbackSymmetry A.hom B.hom).hom`: the library's own lemma `pullbackPairingSymmetry_hom_app_left` proves this by `rfl`. After that one unfolding step, the statement is exactly Mathlib's `pullbackSymmetry_hom_comp_fst` with `f := A.hom` and `g := B.hom`, which says `(pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g`. The library's proof already does just this: one `rw` and then `exact` with the Mathlib lemma. All of the mathematical content is in the Mathlib lemma. The library's definition only wraps the Mathlib isomorphism, so this is a specialization of that lemma to the library's packaging. Since the theorem is stated about the library's own construction, it could instead be read as content of the library's definition, which would make it `none_found`.

### [`LaurentSeries.mem_powerSeries_as_subring_iff`](https://github.com/FormalFrontier/valuation-integers/blob/1a0917cded3bc6936088c5fed8e61963d593d9d7/ValuationIntegers/LaurentSeries.lean#L36-L41) — `formal-frontier-0443`

Snippet: `samples/formal-frontier/formal-frontier-0443.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: LaurentSeries.val_le_one_iff_eq_coe
- **file**: Mathlib/RingTheory/LaurentSeries.lean
- **derivation**: rw [val_le_one_iff_eq_coe K x]
simp only [powerSeries_as_subring, Subring.mem_map, Subring.mem_top, true_and]
- **proof_uses_it**: True
- **explanation**: Mathlib's `val_le_one_iff_eq_coe (f : K⸨X⸩) : Valued.v f ≤ (1 : ℤᵐ⁰) ↔ ∃ F : K⟦X⟧, F = f` is the same statement. `powerSeries_as_subring K` is a Mathlib abbrev for `Subring.map (ofPowerSeries ℤ K) ⊤`, so `x ∈ powerSeries_as_subring K` unfolds to `∃ F, ↑F = x`. The library's theorem is Mathlib's lemma with the sides of the iff swapped and the existential written as membership in Mathlib's own subring alias. No argument is instantiated; the only difference is unfolding a Mathlib definition (a judgment call; `special_case` is the alternative reading). The library's proof already rewrites with this lemma and closes the goal with simp on the definition.

### [`Convexity.StdSimplex.AffineSimplex.face_cone_succ`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Subdivision.lean#L256-L263) — `formal-frontier-0454`

Snippet: `samples/formal-frontier/formal-frontier-0454.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Fin.cons_comp_succ_succAbove
- **file**: Mathlib/Data/Fin/Tuple/Basic.lean
- **derivation**: Fin.cons_comp_succ_succAbove b a i
- **explanation**: This is a duplicate: the library's definitions are thin aliases for Mathlib's tuple operations, and the Mathlib lemma states the same equation.

How the definitions unfold:
- `AffineSimplex m n` is defined as `Fin (n+1) → StdSimplex ℝ (Fin (m+1))`.
- `a.cone b` is defined as `Fin.cases b a`. Mathlib's `Fin.cons b a` is defined as `fun j ↦ Fin.cases b a j`, so the two are definitionally equal.
- `a.face i` is defined as `fun j ↦ a (i.succAbove j)`. This is literally the body of `Fin.removeNth i a`, and it equals `a ∘ i.succAbove`.

So the theorem's left side, `(a.cone b).face i.succ`, unfolds to `Fin.cons b a ∘ i.succ.succAbove`. Its right side, `(a.face i).cone b`, unfolds to `Fin.cons b (i.removeNth a)`.

Mathlib's `Fin.cons_comp_succ_succAbove (x : β) (p : Fin (n+1) → β) (i : Fin (n+1)) : cons x p ∘ i.succ.succAbove = cons x (i.removeNth p)` states exactly this equation, for the same `n`. It needs no instantiation beyond `β := StdSimplex ℝ (Fin (m+1))`, which is just its type parameter.

Because the match only holds up to unfolding, the one-line derivation `Fin.cons_comp_succ_succAbove b a i` relies on the definitional unfolding going through; I could not run Lean to confirm it. If it does not, `by simpa [AffineSimplex.face, AffineSimplex.cone, Fin.removeNth] using Fin.cons_comp_succ_succAbove b a i` should work instead.

The library's current proof does not use this lemma: it argues pointwise with `Fin.cases` and `simp` using `Fin.succ_succAbove_succ`.

### [`Coalgebra.RightComodule.Subcomodule.coaction_mem_range_iff`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean#L472-L475) — `formal-frontier-0496`

Snippet: `samples/formal-frontier/formal-frontier-0496.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.mem_range
- **file**: Mathlib/Algebra/Module/Submodule/Range.lean
- **derivation**: LinearMap.mem_range
- **explanation**: This is a special case of `LinearMap.mem_range : x ∈ range f ↔ ∃ y, f y = x`, with `f := U.toSubmodule.subtype.rTensor C` and `x := X.coaction m`. Like the library's theorem, Mathlib proves `LinearMap.mem_range` by `Iff.rfl`. The library's proof does not cite the lemma: it unfolds the definition directly with `Iff.rfl`. Nothing about comodules is involved; the content is just the definition of membership in the range of a linear map. This is close to the excluded category of generic membership lemmas, so `special_case` is a borderline call. In either reading, the library's theorem is redundant.

### [`SSet.homologyZeroPoint_homology₀Iso`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Reduced.lean#L105-L111) — `formal-frontier-0509`

Snippet: `samples/formal-frontier/formal-frontier-0509.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomologyZero.lean
- **derivation**: by simpa only [homologyZeroPoint, Category.assoc] using SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x
- **proof_uses_it**: True
- **explanation**: The library's `homologyZeroPoint X R x` is defined as the composite `(X.chainComplex R).liftCycles (X.ιChainComplex x) 0 _ _ ≫ (X.chainComplex R).homologyπ 0`. Mathlib's lemma says that this same composite, followed by `(X.homology₀Iso R).hom`, equals `Sigma.ι (fun _ : π₀ X ↦ R) (π₀.mk x)`. Once the definition is unfolded, the two statements are identical up to associativity of composition. The library definition only gives the Mathlib composite a name, so all the mathematical content is in the Mathlib lemma, and the current proof already applies it directly. If unfolding a library definition is not treated as a difference of presentation only, this would instead be a special case with the same one-line derivation.

### [`Matrix.isIdempotentElem_single_one`](https://github.com/FormalFrontier/general-linear-groups/blob/ff8095ef752bcc8bacb5b7b18255fc88470e5e97/GeneralLinearGroups/MatrixCorner.lean#L27-L30) — `formal-frontier-0597`

Snippet: `samples/formal-frontier/formal-frontier-0597.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.single_mul_single_same
- **file**: Mathlib/Data/Matrix/Basis.lean
- **derivation**: by rw [IsIdempotentElem, single_mul_single_same, mul_one]
- **explanation**: Mathlib has no lemma stating directly that a matrix unit is idempotent. I grepped for `IsIdempotentElem` together with `single`, and for `isIdempotentElem_single`. The closest result is `Matrix.single_mul_single_same : single i j c * single j k d = single i k (c * d)`. Taking j = k = i and c = d = 1 gives `single i i 1 * single i i 1 = single i i (1 * 1)`. Rewriting with `mul_one` turns this into `single i i 1`, which is exactly what `IsIdempotentElem` asks for. The library's current proof is a plain `simp [IsIdempotentElem]` and does not cite this lemma explicitly, so `proof_uses_it` is false. Simp most likely closes the goal through it, but that can't be confirmed without running Lean.

### [`CategoryTheory.pullback_eq_inf_of_isPullback`](https://github.com/FormalFrontier/spectral-stone-duality/blob/78b803577679fc37120fa3406833af653fe12018/SpectralStoneDuality/CategoryTheory/Lattice/Extensive.lean#L57-L60) — `formal-frontier-0615`

Snippet: `samples/formal-frontier/formal-frontier-0615.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CategoryTheory.Limits.CompleteLattice.pullback_eq_inf
- **file**: Mathlib/CategoryTheory/Limits/Lattice.lean
- **derivation**: CategoryTheory.Limits.CompleteLattice.pullback_eq_inf f g
- **explanation**: The Mathlib lemma `pullback_eq_inf` has the same hypotheses as the library's theorem: `[SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z)`. It also has the same conclusion, `pullback f g = x ⊓ y`. In both statements the pullback exists because of Mathlib's finite-limits instance for a `SemilatticeInf` with `OrderTop`. The library proves the result differently: it compares limit cones using the library's own `isPullback_inf`, which I did not find in Mathlib. Mathlib's lemma instead computes the limit as a `Finset.inf`. Only the names differ (the library's version adds an `_of_isPullback` suffix and sits in a different namespace).

### [`ProfiniteGrp.closedNormalQuotientProj_isQuotientMap`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ClosedQuotient.lean#L101-L105) — `formal-frontier-0617`

Snippet: `samples/formal-frontier/formal-frontier-0617.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientGroup.isQuotientMap_mk
- **file**: Mathlib/Topology/Algebra/Group/Quotient.lean
- **derivation**: QuotientGroup.isQuotientMap_mk N.toSubgroup
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `QuotientGroup.isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G → G ⧸ N)`. The library defines `closedNormalQuotientProj` as `ConcreteCategory.ofHom ⟨QuotientGroup.mk' N.toSubgroup, QuotientGroup.continuous_mk⟩`, so its underlying function is definitionally `QuotientGroup.mk` for the subgroup `N.toSubgroup`. Taking Mathlib's lemma with `G` as the group underlying the profinite group and the subgroup set to `N.toSubgroup` gives exactly the theorem. The library's current proof is already this one application, closed by unfolding definitions. Mathlib's lemma does not need the normality hypothesis `hN`.

### [`RestrictedProduct.finset_prod_mulSingle_apply`](https://github.com/FormalFrontier/restricted-product-duality/blob/fbdc1f29cfc71cc859ad58b626c847d162be6632/RestrictedProductDuality/CharacterReconstruction.lean#L207-L226) — `formal-frontier-0626`

Snippet: `samples/formal-frontier/formal-frontier-0626.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.prod_pi_mulSingle
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean
- **derivation**: change evalMonoidHom X i (∏ j ∈ s, mulSingle U j (x j)) = _
rw [map_prod]; exact Finset.prod_pi_mulSingle i x s
- **explanation**: I found no lemma in Mathlib for products of `RestrictedProduct.mulSingle`. Its section in `Topology/Algebra/RestrictedProduct/Basic.lean` covers `mulSingle_eq_of_ne`, `mulSingle_mul` and similar, but has nothing about a `Finset` product. The mathematical content is Mathlib's `Finset.prod_pi_mulSingle`: `(∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1`.

The derivation needs only routine glue:
- Evaluating at `i` is the monoid hom `RestrictedProduct.evalMonoidHom`, so `map_prod` moves the product outside the evaluation.
- Each factor `evalMonoidHom X i (mulSingle U j (x j))` is definitionally `Pi.mulSingle j (x j) i`, since `mulSingle` is defined with `val := Pi.mulSingle i x` (see `coe_mulSingle_apply`, proved by `rfl`).

So `Finset.prod_pi_mulSingle i x s` closes the goal, and both statements use classical decidability. If `exact` does not see the definitional equality, `simpa using Finset.prod_pi_mulSingle i x s` should do it, though I could not run Lean to check either version. The library's current proof instead redoes the case split by hand, using `Finset.prod_eq_single_of_mem` and `Finset.prod_eq_one`.

### [`MonoidAlgebra.freeMonoidAugmentation_single`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Free/FreeWordAugmentation.lean#L60-L65) — `formal-frontier-0635`

Snippet: `samples/formal-frontier/formal-frontier-0635.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.liftNCRingHom_single
- **file**: Mathlib/Algebra/MonoidAlgebra/Lift.lean
- **derivation**: simp only [freeMonoidAugmentation, liftNCRingHom_single, RingHom.id_apply]
- **proof_uses_it**: True
- **explanation**: `freeMonoidAugmentation K α` is defined as nothing more than `liftNCRingHom (RingHom.id K) (FreeMonoid.lift fun _ ↦ 0) _`. Mathlib's `liftNCRingHom_single` says `liftNCRingHom f g h (single a b) = f b * g a`. Unfold the definition and take `f := RingHom.id K`, `g := FreeMonoid.lift (fun _ ↦ 0)`, `a := w` and `b := k`; after `RingHom.id_apply` this is exactly the theorem. The library's proof already does this. All the theorem adds to Mathlib's lemma is the choice of arguments in a thin wrapper definition, so it counts as a special case. It is not new content from the library's own definitions.

### [`ValuationSubring.ofPrime_compositeIdeal`](https://github.com/FormalFrontier/adic-modules/blob/6f6fa8b3b08a9dba6faa90e328c8d528645f7d5b/AdicModules/CompositeValuationSubring.lean#L168-L174) — `formal-frontier-0665`

Snippet: `samples/formal-frontier/formal-frontier-0665.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValuationSubring.ofPrime_idealOfLE
- **file**: Mathlib/RingTheory/Valuation/ValuationSubring.lean
- **derivation**: (A.composite W).ofPrime_idealOfLE A (A.composite_le W)
- **proof_uses_it**: True
- **explanation**: Mathlib's `ValuationSubring.ofPrime_idealOfLE` says that for valuation subrings `R ≤ S` of `K`, `ofPrime R (idealOfLE R S h) = S`. In the library, `compositeIdeal A W` is defined as `(A.composite W).idealOfLE A (A.composite_le W)`, so it unfolds by definition to that ideal. The theorem is therefore the Mathlib lemma with `R := A.composite W`, `S := A` and `h := A.composite_le W`. The only non-Mathlib piece is the library's own lemma `composite_le`, passed in as the inclusion hypothesis. All the mathematical content (localizing at that prime gives back the larger ring) comes from the Mathlib lemma. The library's current proof is exactly this one-line application.

### [`AlgebraicGeometry.specialLinearModuleMatrixEquiv_entry`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/SpecialLinearModule.lean#L139-L148) — `formal-frontier-0669`

Snippet: `samples/formal-frontier/formal-frontier-0669.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.toMatrix_apply
- **file**: Mathlib/LinearAlgebra/Matrix/ToLin.lean
- **derivation**: Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq (generalLinearScalarBasis K V indexType basis R) f ▸ LinearMap.toMatrix_apply _ _ _ _ _
- **proof_uses_it**: True
- **explanation**: The library's `specialLinearModuleMatrixEquiv K V indexType basis R` is defined as Mathlib's `(Matrix.SpecialLinearGroup.toLin_equiv b).symm`, where `b = generalLinearScalarBasis K V indexType basis R`. Mathlib's `Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq` is proved by `rfl`. It identifies `(toLin_equiv b).symm g` with `LinearMap.toMatrix b b g`. So once the library definition is unfolded, the theorem is exactly `LinearMap.toMatrix_apply` (`LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i`) with `v₁ = v₂ = b` and `f` the linear map underlying the special linear automorphism. The library's proof already applies `LinearMap.toMatrix_apply`, using the `rfl` lemma only to unfold. The derivation given is that existing one-line proof; I could not run Lean to test a shorter version. The result's only content is that a matrix entry equals the corresponding basis coordinate of the image of a basis vector, which is what `toMatrix_apply` states.

### [`CoalgHom.mem_range`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Hom.lean#L298-L301) — `formal-frontier-0674`

Snippet: `samples/formal-frontier/formal-frontier-0674.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.mem_range
- **file**: Mathlib/Algebra/Module/Submodule/Range.lean
- **derivation**: LinearMap.mem_range (f := f.toLinearMap)
- **proof_uses_it**: True
- **explanation**: `CoalgHom.range` is defined in the library (Hom.lean, line 281) as `Subcoalgebra.mk' (LinearMap.range f.toLinearMap) …`, and I found no `CoalgHom.range` in Mathlib's `RingTheory/Coalgebra`. Membership in this range unfolds definitionally to membership in `LinearMap.range f.toLinearMap`. So the statement is Mathlib's `LinearMap.mem_range` (`y ∈ range f ↔ ∃ x, f x = y`) with `f := f.toLinearMap`, through unfolding the library's wrapper definition. The current proof is exactly that one-line application. This is a borderline case: the lemma is the basic membership lemma for a library-defined structure, but all of its mathematical content comes from `LinearMap.mem_range`.

### [`Subcoalgebra.coe_smul`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra.lean#L266-L268) — `formal-frontier-0685`

Snippet: `samples/formal-frontier/formal-frontier-0685.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SetLike.val_smul
- **file**: Mathlib/GroupTheory/GroupAction/SubMulAction.lean
- **derivation**: SetLike.val_smul D r x
- **explanation**: Mathlib has `SetLike.val_smul`: for `[SMul R M] [SetLike S M] [SMulMemClass S R M] (s : S) (r : R) (x : s)`, it states `(↑(r • x) : M) = r • (x : M)`. Its proof is `rfl`. The library registers `SMulMemClass (Subcoalgebra K C) K C` (line 108), so setting `S := Subcoalgebra K C`, `R := K`, `M := C` and `s := D` gives exactly `Subcoalgebra.coe_smul`.

One caveat: the theorem's `•` on `D` probably elaborates through the library's own `Module K D` instance (`D.toSubmodule.module`). Mathlib's lemma uses `SetLike.smul`, a priority-50 instance. Both reduce to `⟨r • x.1, _⟩`, which is why the library's `rfl` proof works. So `exact SetLike.val_smul D r x` should go through by definitional unfolding, but a syntactic `rw` might not match the instances.

This is a special case rather than a duplicate because the abstract `SetLike` type `S` has to be set to `Subcoalgebra K C`. The current proof is `rfl` and does not cite the Mathlib lemma.

### [`TopCat.singularHomologyZeroPoint_augmentation`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Reduced.lean#L161-L170) — `formal-frontier-0689`

Snippet: `samples/formal-frontier/formal-frontier-0689.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomologyZero.lean
- **derivation**: simpa only [singularHomologyZeroPoint, SSet.homologyZeroPoint, singularHomology₀ε, Category.assoc] using SSet.liftCycles_ιChainComplex_homologyPi_homology₀ε (toSSet.obj X) singularHomologyIntegerCoefficients (toSSetObj₀Equiv.symm x)
- **explanation**: The theorem is a special case of the Mathlib lemma `SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε` (in `Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomologyZero.lean`), which proves `liftCycles (X.ιChainComplex x) 0 _ _ ≫ homologyπ 0 ≫ X.homology₀ε R = 𝟙 R` for any simplicial set `X` and 0-simplex `x`.

The library's definitions add no mathematical content:
- `TopCat.singularHomologyZeroPoint X x` is defined as `SSet.homologyZeroPoint (toSSet.obj X) ℤ (toSSetObj₀Equiv.symm x)`.
- `SSet.homologyZeroPoint` is literally the composite `liftCycles … ≫ homologyπ 0`.
- Mathlib defines `TopCat.singularHomology₀ε X R` as `(toSSet.obj X).homology₀ε R`.

So once these are unfolded, the theorem is the Mathlib lemma with `X := toSSet.obj X`, `R := singularHomologyIntegerCoefficients` and `x := toSSetObj₀Equiv.symm x`; the two composites differ only by associativity (`Category.assoc`).

The current proof does not cite the Mathlib lemma directly. It goes through the library's `SSet.homologyZeroPoint_augmentation`, which is itself proved by `simpa` from the Mathlib lemma.

**Caveat on the derivation:** I could not run Lean, so the derivation is untested. It also has a typo: it writes `homologyPi` where the lemma name uses `homologyπ`, and should read `SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε (toSSet.obj X) singularHomologyIntegerCoefficients (toSSetObj₀Equiv.symm x)`. If `simpa only` does not unfold the `show` in the library definition, a `change` step like the one in the current proof may be needed first.

### [`AlgebraicGeometry.unitriangularStageFromGL_comp_quotient`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularStages.lean#L148-L152) — `formal-frontier-0692`

Snippet: `samples/formal-frontier/formal-frontier-0692.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.liftₐ_comp
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.Quotient.liftₐ_comp _ _ _
- **proof_uses_it**: True
- **explanation**: The library defines `unitriangularStageFromGL K n r R s` as `Ideal.Quotient.liftₐ (ideal K n r) (unitriangularFromGL K (Fin n) R s.1) _`. Presumably `quotient K n r` is the quotient map `Ideal.Quotient.mkₐ K (ideal K n r)`; I did not open its definition, but the one-term proof only typechecks if it unfolds to that. Mathlib's `Ideal.Quotient.liftₐ_comp` says `(Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f`. Taking I = ideal K n r and f = unitriangularFromGL K (Fin n) R s.1 gives exactly the theorem, so it is a special case. The library's proof is already this single application. This is a borderline call: the theorem amounts to the quotient's lift property applied to the library's own definition, so it could also be read as "content lies in the library's definitions". The match itself is exact.

### [`Subcoalgebra.map_le_iff`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Map.lean#L121-L130) — `formal-frontier-0724`

Snippet: `samples/formal-frontier/formal-frontier-0724.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.map_le_iff_le_comap
- **file**: Mathlib/Algebra/Module/Submodule/Map.lean
- **derivation**: Submodule.map_le_iff_le_comap (f := f.toLinearMap) (p := D.toSubmodule) (q := S)
- **explanation**: The library defines `(Subcoalgebra.map f D).toSubmodule` as `Submodule.map f.toLinearMap D.toSubmodule`, and `map_toSubmodule` shows this holds by `rfl`. So the left-hand side is `Submodule.map f.toLinearMap D.toSubmodule ≤ S`. Mathlib's `Submodule.map_le_iff_le_comap` says this is equivalent to `D.toSubmodule ≤ Submodule.comap f.toLinearMap S`. Unfolding `≤` and `mem_comap` turns the right-hand side into `∀ x ∈ D, f x ∈ S`; this assumes membership in a subcoalgebra unfolds to membership in its underlying submodule, as the `SetLike` setup suggests. So the theorem is Mathlib's lemma with `f` instantiated to `f.toLinearMap`, and should go through by definitional unfolding. This is not checked: I could not run Lean, and I did not read the `SetLike` instance itself. If the term does not elaborate as written, `simpa [map_toSubmodule] using Submodule.map_le_iff_le_comap` should work instead. At bottom this is `Set.image_subset_iff`, which is also how Mathlib proves the lemma. The library's current proof works by hand through `mem_map` and does not use the Mathlib lemma.

### [`AlgebraicGeometry.sourceOrderTensor_smul_tmul`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/MatrixEndBaseChange.lean#L58-L62) — `formal-frontier-0727`

Snippet: `samples/formal-frontier/formal-frontier-0727.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.smul_tmul'
- **file**: Mathlib/LinearAlgebra/TensorProduct/Defs.lean
- **derivation**: show r • (s ⊗ₜ[K] v) = (r * s) ⊗ₜ[K] v
exact TensorProduct.smul_tmul' r s v
- **proof_uses_it**: True
- **explanation**: This is a borderline call. `sourceOrderTensorEquiv` is defined as `TensorProduct.comm K V R`, so it sends `v ⊗ₜ s` to `s ⊗ₜ v`. Once that is unfolded, the statement reads `r • (s ⊗ₜ v) = (r * s) ⊗ₜ v` in `R ⊗[K] V`. That is `TensorProduct.smul_tmul'` (`r • m ⊗ₜ n = (r • m) ⊗ₜ n`) with the left factor `M := R`. The step from `r • s` to `r * s` holds by definition (`smul_eq_mul`). The library's proof already uses `smul_tmul'` through `simp`. I chose special_case over none_found because `smul_tmul'` carries the result's actual content (the scalar action on a tensor product acts on the left factor), and the library's own definition only adds a factor swap. Caveats: `smul_tmul'` is proved by `rfl`, so it just restates how the action is defined, and the library statement is probably true by `rfl` as well. The two-line derivation above has not been compiled.

### [`RingedSpaces.Modules.tensorSectionHomEquiv_apply`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/PresheafChangeOfRings.lean#L77-L83) — `formal-frontier-0738`

Snippet: `samples/formal-frontier/formal-frontier-0738.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
- **file**: Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean
- **derivation**: letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U)); letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
exact ModuleCat.extendRestrictScalarsAdj_homEquiv_apply t m
- **proof_uses_it**: True
- **explanation**: `tensorSection`, `tensorUnitSection` and `tensorSectionHomEquiv` are thin wrappers. They are, respectively, `(extendScalars f).obj (M.obj U)`, the unit of `extendRestrictScalarsAdj f` at `M.obj U`, and `(extendRestrictScalarsAdj f).homEquiv`, where `f = ((ringMap A B theta).app U).hom`. Mathlib's lemma says `(extendRestrictScalarsAdj f).homEquiv _ _ φ m = φ ((1 : S) ⊗ₜ m)` for any ring hom `f` between commutative rings. The unit sends `m` to `1 ⊗ₜ m` by definition, and Mathlib's lemma is itself proved by `rfl`. So the library theorem is Mathlib's lemma with `f` set to this particular section map. The library's proof already applies it directly, after installing the `CommRing` instances on the sections. Strictly speaking, the derivation takes three tactic steps (two `letI`s plus the `exact`) rather than two lines. The `letI`s only provide instances, though, so the derivation is still routine glue.

### [`RingedSpaces.Modules.SheafInverseImage.pointwiseToPullbackFac`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/SheafInverseImage.lean#L239-L253) — `formal-frontier-0740`

Snippet: `samples/formal-frontier/formal-frontier-0740.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Functor.descOfIsLeftKanExtension_fac
- **file**: Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean
- **derivation**: by simpa only [PresheafInverseImage.pointwiseToPullback, Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso, Iso.refl_hom, Category.id_comp] using Functor.descOfIsLeftKanExtension_fac _ ((Opens.map f).op.pointwiseLeftKanExtensionUnit P) _ ((Opens.map f).op.leftKanExtensionUnit P)
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Functor.descOfIsLeftKanExtension_fac`. The library's `PresheafInverseImage.pointwiseToPullback f C P` is defined as Mathlib's `Functor.leftKanExtensionUnique`. That comparison iso goes from the pointwise left Kan extension (with `pointwiseLeftKanExtensionUnit P`) to the chosen `leftKanExtension` (with `leftKanExtensionUnit P`). By `leftKanExtensionUniqueOfIso`, its `hom` is `descOfIsLeftKanExtension _ α G' (𝟙 ≫ β)`. So once the definition is unfolded and `Iso.refl_hom` and `Category.id_comp` are simplified, the statement is exactly `descOfIsLeftKanExtension_fac` with α the pointwise unit, G the chosen left Kan extension and β its unit. I did not find a separate Mathlib lemma stating this factorization for `leftKanExtensionUnique.hom` directly. The library's current proof is already this one-line `simpa` using that lemma.

### [`Subgroup.RightTransversal.changeFactor_mul_changeRep`](https://github.com/FormalFrontier/group-theory/blob/2b14628cb53e79783bd51baadcb4fc85667c8da3/GroupTheory/Transversal.lean#L115-L117) — `formal-frontier-0825`

Snippet: `samples/formal-frontier/formal-frontier-0825.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.IsComplement.equiv_fst_mul_equiv_snd
- **file**: Mathlib/GroupTheory/Complement.lean
- **derivation**: S.2.equiv_fst_mul_equiv_snd _
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`. The Mathlib lemma says `↑(hST.equiv g).fst * ↑(hST.equiv g).snd = g` for any proof `hST` that two sets are complements and any `g : G`. In the library, `changeFactor T S t` is defined as `(S.2.equiv (t : G)).1` and `changeRep T S t` as `(S.2.equiv (t : G)).2`. So once those two definitions are unfolded, the theorem is the Mathlib lemma with `hST := S.2` (the complement proof that comes with the right transversal `S`) and `g := ↑t`. The library's current proof is exactly that one application: `S.2.equiv_fst_mul_equiv_snd _`. Since `changeFactor` and `changeRep` only rename the two coordinates of Mathlib's `IsComplement.equiv`, the mathematical content of the theorem comes from the Mathlib lemma.

### [`TopModuleCat.algebraMap_mulAction_eq_smul`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/Topology/Restriction.lean#L393-L400) — `formal-frontier-0840`

Snippet: `samples/formal-frontier/formal-frontier-0840.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.smul_def
- **file**: Mathlib/Algebra/Algebra/Defs.lean
- **derivation**: funext p; exact (Algebra.smul_def p.1 p.2).symm
- **proof_uses_it**: True
- **explanation**: The theorem follows from `Algebra.smul_def` (Mathlib/Algebra/Algebra/Defs.lean): `Algebra.smul_def (r : R) (x : A) : r • x = algebraMap R A r * x`. The theorem states the same identity for functions on `R × S`. To get it, apply `funext` and use `smul_def` at `p.1` and `p.2`, with the sides swapped. The library's proof already does exactly this. I did not find a version stated for functions in Mathlib; a grep for `algebraMap _ _ _.1 * _.2` found only an unrelated use. Because going from a pointwise equation to an equation of functions is more than a change of presentation, the verdict is `special_case` rather than `duplicate`.

### [`UnitriangularStageCoordinateRing.survivingInclusion_injective`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/UnitriangularStagePolynomial.lean#L49-L50) — `formal-frontier-0862`

Snippet: `samples/formal-frontier/formal-frontier-0862.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subtype.val_injective
- **file**: Mathlib/Data/Subtype.lean
- **derivation**: Subtype.val_injective
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `Subtype.val_injective`. The library defines `survivingInclusion n r` as `Subtype.val` on the subtype `{p : StrictUpperPair (Fin n) // p.1.1.val + r ≤ p.1.2.val}`. So the theorem is `Subtype.val_injective : Injective (@Subtype.val _ p)`, with the predicate `p` set to this particular index-gap condition and the definition unfolded. The current proof is already exactly `Subtype.val_injective`.

### [`DirectLimit.VaryingScalar.of_map`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/VaryingScalar.lean#L127-L129) — `formal-frontier-0897`

Snippet: `samples/formal-frontier/formal-frontier-0897.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DirectLimit.eq_of_le
- **file**: Mathlib/Order/DirectedInverseSystem.lean
- **derivation**: (DirectLimit.eq_of_le ⟨i, m⟩ j hij).symm
- **proof_uses_it**: True
- **explanation**: This is a special case of Mathlib's `DirectLimit.eq_of_le`, and the current proof already uses that lemma. The Mathlib lemma says `(⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧` whenever `x.1 ≤ i`. The library's `of A f M g i m` is defined to be `⟦⟨i, m⟩⟧`, as recorded by `of_apply`, which is proved by `rfl`. Once `of` is unfolded, `of_map` reads `⟦⟨j, g i j hij m⟩⟧ = ⟦⟨i, m⟩⟧`. That is `eq_of_le` with `F := M`, the transition maps taken to be the coerced `g`, and `x := ⟨i, m⟩`, with the two sides swapped (`.symm`). The library's only additions are the wrapper `of` and the varying-scalar setting; neither adds to the mathematical content, which lies entirely in `eq_of_le`.

### [`ModuleCat.piRightSingle_add`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Module/RightProduct.lean#L478-L482) — `formal-frontier-0906`

Snippet: `samples/formal-frontier/formal-frontier-0906.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.single_add
- **file**: Mathlib/Algebra/Group/Pi/Lemmas.lean
- **derivation**: classical
exact Pi.single_add (f := fun j => (Mi j : Type uM)) i x y
- **proof_uses_it**: True
- **explanation**: The library's `piRightSingle Ri Mi i x` is defined as `Pi.single i x`, using `Classical.decEq ι`, into `∀ i, Mi i`. Its codomain is `piRight`, which is `ModuleCat.of _ (∀ i, Mi i)`. `Pi.single_add` is generated by `to_additive` from `Pi.mulSingle_mul` (Mathlib/Algebra/Group/Pi/Lemmas.lean, line 300). It states `Pi.single i (x + y) = Pi.single i x + Pi.single i y` for any family `f` with `[∀ i, AddZeroClass (f i)]` and `[DecidableEq I]`. The library theorem is that lemma with the family `f` set to `fun j => Mi j`, once `piRightSingle` is unfolded. The current proof does exactly this.

### [`SphereTopology.sphere2NorthVector_norm`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Sphere.lean#L55-L56) — `formal-frontier-0912`

Snippet: `samples/formal-frontier/formal-frontier-0912.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.norm_single
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: by rw [sphere2NorthVector, PiLp.norm_single, norm_one]
- **proof_uses_it**: True
- **explanation**: The theorem is a special case of Mathlib's `PiLp.norm_single`, which states `‖PiLp.single p i b‖ = ‖b‖`. The library defines `sphere2NorthVector := PiLp.single 2 2 1` in `EuclideanSpace ℝ (Fin 3)`. Taking p = 2, i = 2 and b = (1 : ℝ) in `PiLp.norm_single` gives `‖sphere2NorthVector‖ = ‖(1 : ℝ)‖`, and `norm_one` turns the right-hand side into 1. The library's proof is `simp [sphere2NorthVector]`. I have not run it, but since `PiLp.norm_single` is tagged `@[simp]`, it is very likely the lemma `simp` uses here. That is why `proof_uses_it` is set to true.

### [`AlgebraicGeometry.powerRootAlgebra_free`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/PowerImage.lean#L119-L123) — `formal-frontier-0921`

Snippet: `samples/formal-frontier/formal-frontier-0921.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.Monic.free_adjoinRoot
- **file**: Mathlib/RingTheory/AdjoinRoot.lean
- **derivation**: (Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)).free_adjoinRoot
- **proof_uses_it**: True
- **explanation**: The library's `powerRootPolynomial K n A a` is defined as `X ^ n - C (a : A.obj)`. Mathlib's `Polynomial.Monic.free_adjoinRoot (hg : g.Monic) : Module.Free R (AdjoinRoot g)` holds for any monic `g` over a commutative ring. The theorem is that lemma with `g` set to `X ^ n - C a`. The only side condition is that this polynomial is monic. Mathlib's `Polynomial.monic_X_pow_sub_C` supplies it from `n ≠ 0`, and `n ≠ 0` comes from `0 < n`. The library's one-line proof already does exactly this, so the theorem is a direct instance of the Mathlib lemma.

### [`Steinberg.lift_unique`](https://github.com/FormalFrontier/general-linear-groups/blob/ff8095ef752bcc8bacb5b7b18255fc88470e5e97/GeneralLinearGroups/Steinberg.lean#L154-L161) — `formal-frontier-0924`

Snippet: `samples/formal-frontier/formal-frontier-0924.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PresentedGroup.toGroup.unique
- **file**: Mathlib/GroupTheory/PresentedGroup.lean
- **derivation**: MonoidHom.ext fun _ => PresentedGroup.toGroup.unique _ φ fun x => hφ x.1 x.2
- **explanation**: This is a borderline call. `Presented ι R` is an abbreviation for `PresentedGroup relations`, and `lift f ...` is defined as `PresentedGroup.toGroup` applied to the uncurried family `fun gen => f gen.1 gen.2`. Mathlib's `PresentedGroup.toGroup.unique` says that any hom `g` with `g (of x) = f x` for all `x` satisfies `g x = toGroup h x` for every `x`. The library theorem is that statement with `rels := relations` and the uncurried `f`. Applying `MonoidHom.ext` turns the pointwise equality into equality of homs. The relation-proof argument is left as `_`, and proof irrelevance makes it match the proof inside `lift`. `hφ x.1 x.2` gives the generator hypothesis, since `generator x.1 x.2` unfolds to `PresentedGroup.of x` by structure eta. I have not compiled this derivation. The library's proof uses its own `hom_ext` (built on `PresentedGroup.ext`) and `lift_generator` (built on `PresentedGroup.toGroup.of`), not `toGroup.unique` directly. It is borderline because `toGroup.unique` is close to an ext-style universal-property lemma. Still, the theorem adds no mathematical content specific to Steinberg groups beyond this instantiation.

### [`Nat.PowerIndex.mul_le_right`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ProcyclicPowerLimit.lean#L95-L97) — `formal-frontier-0938`

Snippet: `samples/formal-frontier/formal-frontier-0938.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.dvd_mul_left
- **file**: Init/Data/Nat/Dvd.lean
- **derivation**: Nat.dvd_mul_left d.val n.val
- **explanation**: This is a borderline call. `PowerIndex S` is the library's own type. Its order is defined as reverse divisibility (`n ≤ d` means `d.val ∣ n.val`), and `(n * d).val` is defined as `n.val * d.val`. Both definitions unfold by `rfl`, so the goal `n * d ≤ d` is definitionally `d.val ∣ n.val * d.val`. That is exactly the Lean core lemma `Nat.dvd_mul_left (a b : Nat) : a ∣ b * a`, with `a := d.val` and `b := n.val`. The derivation needs only definitional unfolding, which counts as allowed glue. I have not compiled the one-line derivation, though I expect the unfolding to go through. The current proof does not cite the lemma. Instead it gives the witness `⟨n.val, …⟩` by hand and closes the remaining goal with `mul_comm`, which is just `Nat.dvd_mul_left` written out. One could also argue that the order wrapper is the library's own content, which would make this `none_found`. I chose `special_case` because, once the definitions are unfolded, the only mathematical fact left is `d ∣ n * d`.

### [`LinearMap.postcomp_injective`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Module/HomExact.lean#L48-L51) — `formal-frontier-0963`

Snippet: `samples/formal-frontier/formal-frontier-0963.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Function.Injective.injective_linearMapComp_left
- **file**: Mathlib/Algebra/Module/LinearMap/Defs.lean
- **derivation**: hi.injective_linearMapComp_left
- **proof_uses_it**: True
- **explanation**: This is a duplicate, and the library's proof already applies the Mathlib lemma directly. Mathlib's `Function.Injective.injective_linearMapComp_left` says: if `f` is injective, then `fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g` is injective. The library's `postcomp i` is its own `AddMonoidHom` wrapper. Its coercion to a function is, by definition, `fun g => i.comp g`, which is what lets the proof term go through unchanged. The library's statement is the linear case of Mathlib's semilinear one. `→ₗ[R]` is notation for `→ₛₗ[RingHom.id R]`, so Mathlib's lemma covers this setting as it stands. The only difference is that the library wraps the map in its own definition, which is presentation, not new mathematical content.

### [`TopModuleCat.tensorProdRight_symm_tmul`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/Topology/TensorProduct/Prod.lean#L233-L240) — `formal-frontier-0987`

Snippet: `samples/formal-frontier/formal-frontier-0987.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.prodRight_symm_tmul
- **file**: Mathlib/LinearAlgebra/TensorProduct/Prod.lean
- **derivation**: by rw [tensorProdRight_symm_apply]; exact TensorProduct.prodRight_symm_tmul R R C M N c m n
- **proof_uses_it**: True
- **explanation**: The library's `tensorProdRight` is a `ContinuousLinearEquiv`. Its underlying linear equivalence is, by definition, Mathlib's `TensorProduct.prodRight R R C M N`. The lemma `tensorProdRight_symm_apply` states this for the inverse and is proved by `rfl`. Mathlib's `TensorProduct.prodRight_symm_tmul (m₁ m₂ m₃) : (prodRight R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, m₁ ⊗ₜ m₃) = m₁ ⊗ₜ (m₂, m₃)` is exactly this statement, taken with S := R, M₁ := C, M₂ := M, M₃ := N. The library's statement is about its own wrapper around the equivalence rather than about Mathlib's object, so this is not a literal duplicate. Unfolding the wrapper is the only step needed, and its docstring calls it "the continuous realization of Mathlib's `TensorProduct.prodRight_symm_tmul`". The current proof is this two-step derivation already: rewrite with `tensorProdRight_symm_apply`, then apply the Mathlib lemma.

