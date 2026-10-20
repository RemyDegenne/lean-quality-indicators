# duplicates-mathlib: run `main`, judge `claude-opus-5-5-high`

| Library | Sampled | Judged | Flagged | `duplicate` | `special_case` | `proof_uses_it` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Tau Ceti | 400 | 400 | 16 | 0 | 16 | 12 | 4.0% | 2.5%–6.4% | $19.10 |
| Lean Pool | 400 | 400 | 22 | 2 | 20 | 10 | 5.5% | 3.7%–8.2% | $15.71 |
| FLT (Anthropic) | 400 | 400 | 50 | 5 | 45 | 23 | 12.5% | 9.6%–16.1% | $27.66 |
| Formal Frontier | 400 | 400 | 16 | 0 | 16 | 9 | 4.0% | 2.5%–6.4% | $22.42 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Tau Ceti (16 flagged)

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


## Lean Pool (22 flagged)

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


## FLT (Anthropic) (50 flagged)

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


## Formal Frontier (16 flagged)

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

