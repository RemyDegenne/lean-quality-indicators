# definition-fidelity: run `defs1`, judge `claude-opus-5-5-high`

| Library | Sampled | Judged | `not_a_mathematical_object` | `unclear` | Assessed | Flagged | `incorrect` | `too_narrow` | `no_docstring` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 1000 | 170 | 0 | 830 | 10 | 2 | 6 | 2 | 1.2% | 0.7%–2.2% | $45.24 |
| Tau Ceti | 1000 | 1000 | 88 | 0 | 912 | 11 | 1 | 10 | 0 | 1.2% | 0.7%–2.1% | $117.32 |
| Lean Pool | 1000 | 1000 | 615 | 0 | 385 | 33 | 3 | 29 | 1 | 8.6% | 6.2%–11.8% | $70.87 |
| FLT (Anthropic) | 1000 | 1000 | 0 | 0 | 1000 | 1000 | 0 | 0 | 1000 | 100.0% | 99.6%–100.0% | $0.00 |
| Formal Frontier | 1000 | 1000 | 231 | 0 | 769 | 41 | 0 | 29 | 12 | 5.3% | 4.0%–7.2% | $102.71 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (10 flagged)

### [`nullSubgroup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Group/NullSubmodule.lean#L36-L46) — `mathlib-0023`

Snippet: `samples/mathlib/mathlib-0023.lean`

- **verdict**: `too_narrow`
- **intended_object**: The null subgroup of a seminormed group M: the subgroup {x ∈ M | ‖x‖ = 0} (the kernel of the seminorm). Inferred from the docstring, the module docs and the name.
- **explanation**: The definition is correct: the carrier is {x | ‖x‖ = 0}. Closure under the group operations follows from norm_one', the triangle inequality norm_mul_le' and norm_inv'. However, the definition assumes [SeminormedCommGroup M], while all three lemmas it uses are stated in Mathlib for an arbitrary [SeminormedGroup E] (section SeminormedGroup in Mathlib/Analysis/Normed/Group/Basic.lean). Commutativity is never used, and the same body compiles verbatim for SeminormedGroup. The null subgroup of a group seminorm is a standard notion for non-abelian groups as well. In a seminormed group it equals the closure of {1}, since ‖x‖ = dist(x, 1), and that closure is even a normal subgroup. So the multiplicative definition should be stated for SeminormedGroup. The additive version derived from it can still be specialized for the submodule part, which genuinely needs commutativity. No other Mathlib declaration defines this subgroup.

### [`Traversable.foldMap`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Fold.lean#L187-L188) — `mathlib-0125`

Snippet: `samples/mathlib/mathlib-0125.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ofCompactSupport`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/ContinuousMap/BoundedCompactlySupported.lean#L81-L93) — `mathlib-0166`

Snippet: `samples/mathlib/mathlib-0166.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical inclusion of compactly supported continuous functions into bounded continuous functions: a continuous g : α → γ with compact support is bounded, so it gives an element of C_b(α, γ). Inferred from the docstring and name.
- **explanation**: The definition is mathematically correct. Boundedness is proved by taking the maximum of ‖g‖ on the compact set tsupport g (or noting that g = 0 if the support is empty), then using dist_le_two_norm'. But γ is required to be a NonUnitalNormedRing, and the body never uses multiplication. It only needs Zero (for HasCompactSupport and image_eq_zero_of_notMem_tsupport), a norm (Continuous.norm, maximising ‖g‖) and dist_le_two_norm', which holds in any SeminormedAddGroup. The ring assumption is inherited from the section's `variable` line, which the rest of the file needs to build the ideal C_cb(α, γ), not this constructor. The fact C_c ⊆ C_b is standard for functions valued in a normed group or normed space, and Mathlib states the related lemma Continuous.bounded_above_of_compact_support for normed groups. So this constructor should be stated for [SeminormedAddGroup γ]. Mathlib has no general counterpart: CompactlySupportedContinuousMap has no map to α →ᵇ β, and the only similar constructors are BoundedContinuousFunction.mkOfCompact (compact domain) and ZeroAtInfty.toBCF.

### [`CategoryTheory.IsUniversallyEffectiveEquivalenceRelationCategory`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/EquivalenceRelation.lean#L295-L300) — `mathlib-0247`

Snippet: `samples/mathlib/mathlib-0247.lean`

- **verdict**: `incorrect`
- **intended_object**: A category in which every internal equivalence relation R ⇉ A, for all objects R and A, is universally effective: it has a quotient π : A → B that is both a kernel-pair and a pushout square, and π is a universal (pullback-stable) effective epimorphism. This is a "universally exact"-type property of C, taken from the docstring.
- **explanation**: The class means to say something about the whole category C, quantifying over all objects R and A. But R and A are not bound in the field. The field `isUniversallyEffectiveEquivalenceRelation (p₁ p₂ : R ⟶ A) [IsEquivalenceRelation p₁ p₂] : …` only rebinds p₁ and p₂, which shadow the section variables of the same name. R and A are the section variables `{R A : C}` declared earlier (`variable {R A : C} (p₁ p₂ : R ⟶ A)`).

In Lean 4, when a structure or class field mentions a section variable, that variable becomes a parameter of the structure. So the class is actually `IsUniversallyEffectiveEquivalenceRelationCategory (C) [Category C] {R A : C}`. It only says that, for one fixed pair of objects R and A, every equivalence relation R ⇉ A is universally effective. The intended statement is about all equivalence relations in C.

Concrete discrepancy: take a category with an equivalence relation on some pair (R', A') that is not effective. If every equivalence relation on another pair (R, A) is universally effective, the class can still hold at (R, A), yet C is not "universally exact". The implicit parameters R and A also cannot be inferred from `IsUniversallyEffectiveEquivalenceRelationCategory C`, which confirms the binders are misplaced; they should be `∀ {R A : C}` inside the field. The library never uses the class, so nothing compensates for this.

There is also a lesser point: the name "universally exact" is not standard, and the usual Barr-exact notion also asks for finite limits / regularity. But the scoping bug alone means the definition does not formalize the intended property.

### [`Finsupp.fun₀.matchAlts`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finsupp/Notation.lean#L27-L29) — `mathlib-0360`

Snippet: `samples/mathlib/mathlib-0360.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LieRing.ofAssociativeRing`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Lie/OfAssociative.lean#L45-L52) — `mathlib-0444`

Snippet: `samples/mathlib/mathlib-0444.lean`

- **verdict**: `too_narrow`
- **intended_object**: The commutator Lie ring of an associative ring A: the additive group of A with bracket [x, y] = xy − yx. This comes from the docstring and the module documentation.
- **explanation**: The construction is mathematically correct. The bracket comes from `Ring.instBracket`, which gives ⁅x, y⁆ = x*y - y*x. The four axioms are proved from distributivity, `mul_sub_left_distrib`/`mul_sub_right_distrib`, `mul_assoc`, `sub_self` and `abel`. So for every `Ring A` this is exactly the commutator Lie ring.

The definition assumes `[Ring A]`, but neither the construction nor the proofs use the multiplicative identity (`one_mul`, `mul_one`, `1`). They only need an associative, distributive multiplication on an additive commutative group, which is exactly Mathlib's `NonUnitalRing`.

Mathlib itself defines the underlying bracket `Ring.instBracket` and `Ring.lie_def` under `[NonUnitalNonAssocRing R]` (in Mathlib/Algebra/Ring/Commute.lean). Only associativity needs to be added to get the Lie ring structure.

In the literature, the commutator Lie algebra A⁻ is formed for any associative ring or algebra, unital or not. Examples are ideals, strictly upper-triangular matrices and non-unital operator algebras. So the natural generality is `NonUnitalRing A`. Requiring a unit is a strictly stronger hypothesis than the construction needs. Hence the verdict is `too_narrow`, not `incorrect`.

I found no separate Mathlib declaration giving this Lie ring for non-unital rings.

### [`SSet.Truncated.rightExtensionInclusion`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean#L39-L44) — `mathlib-0532`

Snippet: `samples/mathlib/mathlib-0532.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical right extension of the restriction X ∘ (inclusion of the n-truncated simplex category)^op along that inclusion, given by X itself with the identity natural transformation. It is the datum used to state that X is n-coskeletal. Inferred from the docstring and the module documentation.
- **mathlib_counterpart**: CategoryTheory.SimplicialObject.Truncated.rightExtensionInclusion
- **explanation**: The body is `RightExtension.mk _ (𝟙 _)` for X : SSet, which correctly gives X with the identity transformation as a right extension of its n-truncation along `(Truncated.inclusion n).op`. Mathlib already has the same construction, with the same body and docstring, for any simplicial object in an arbitrary category C: `CategoryTheory.SimplicialObject.Truncated.rightExtensionInclusion` in `Mathlib/AlgebraicTopology/SimplicialObject/Coskeletal.lean`. The definition uses nothing specific to sets. It only needs a functor SimplexCategoryᵒᵖ ⥤ C and an identity natural transformation. So it is the special case C = Type u of a construction Mathlib provides in general.

### [`MulAut.congr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/End.lean#L743-L751) — `mathlib-0635`

Snippet: `samples/mathlib/mathlib-0635.lean`

- **verdict**: `too_narrow`
- **intended_object**: The isomorphism Aut(G) ≃* Aut(H), f ↦ φ ∘ f ∘ φ⁻¹, induced by an isomorphism φ : G ≃* H. This is inferred from the docstring ("Isomorphic groups have isomorphic automorphism groups") and the name.
- **explanation**: The body is correct: toFun f = φ ∘ f ∘ φ⁻¹ and invFun f = φ⁻¹ ∘ f ∘ φ, and conjugating by φ respects composition, which is the multiplication in MulAut. However, the hypotheses `[Group G]` and `[Group H]` are never used. The construction uses only MulEquiv.trans and MulEquiv.symm. MulAut M and its group structure are defined in the same namespace for any `[Mul M]`, and the simp proofs rely only on generic MulEquiv lemmas. So the same definition works for any magmas, with an isomorphism φ : M ≃* N giving MulAut M ≃* MulAut N, and should be stated with `[Mul G] [Mul H]`. The analogous AlgEquiv.autCongr is stated in its full natural generality. A search found no other Mathlib declaration of type `MulAut _ ≃* MulAut _`, so this one is the only version and it is needlessly restricted to groups.

### [`ContinuousMultilinearMap.currySumEquiv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean#L546-L569) — `mathlib-0641`

Snippet: `samples/mathlib/mathlib-0641.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical currying isometry L(∏_{i∈ι⊕ι'} E_i; G') ≅ L(∏_{i∈ι} E_i; L(∏_{j∈ι'} E_j; G')), which identifies continuous multilinear maps on variables indexed by ι ⊕ ι' with continuous multilinear maps on the ι-variables whose values are continuous multilinear maps on the ι'-variables. Inferred from the docstring and the name.
- **mathlib_counterpart**: MultilinearMap.currySumEquiv
- **explanation**: The map is correct. It sends `currySum f` to `fun m m' => f (Sum.elim m m')`, its inverse is `uncurrySum`, and the norm bounds hold in both directions, so it is a linear isometric equivalence. The problem is that it only covers a constant family of domain spaces (`fun _ : ι ⊕ ι' => G`).

Nothing in the construction needs every variable to live in the same space G:
- The bound ‖f(m)‖ ≤ ‖f‖ ∏ ‖m_i‖ holds for any family E : ι ⊕ ι' → Type of normed spaces.
- The bound splits over the sum type by `Fintype.prod_sum_type`.
- `MultilinearMap.mkContinuousMultilinear`, `mkContinuous` and their norm lemmas already take arbitrary families E, E'.
- The algebraic layer is already general: `MultilinearMap.currySum`, `uncurrySum` and `currySumEquiv` (Mathlib/LinearAlgebra/Multilinear/Curry.lean) are stated for any `N : ι ⊕ ι' → Type*`, with target `MultilinearMap R (fun i => N (.inl i)) (MultilinearMap R (fun i => N (.inr i)) M₂)`.
- In this same file, the `Fin`-indexed currying isometries (`curryLeft`/`curryRight` and their equivalences) use a general family `Ei`.

The textbook statement L(E_1,…,E_n; G) ≅ L(E_1,…,E_k; L(E_{k+1},…,E_n; G)) is also heterogeneous. So the natural generality is a family E : ι ⊕ ι' → Type of normed spaces, with target ContinuousMultilinearMap 𝕜 (fun i => E (.inl i)) (ContinuousMultilinearMap 𝕜 (fun i => E (.inr i)) G'). The constant family is not needed for the definition's content. It is needed only by downstream uses such as `curryFinFinset`, and the general version would cover those as a special case.

### [`CategoryTheory.FilteredObject.isStrictHom`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Filtration/Basic.lean#L158-L161) — `mathlib-0677`

Snippet: `samples/mathlib/mathlib-0677.lean`

- **verdict**: `incorrect`
- **intended_object**: The class (morphism property) of strict morphisms of filtered objects in the sense of Deligne (Théorie de Hodge II, cited in the module doc): f : (X,F) → (Y,F) is strict if f(F_i X) = f(X) ∩ F_i Y for all i (equivalently Coim f → Im f is a filtered isomorphism). Inferred from the docstring "strict morphisms of filtered objects", the name, and the module reference.
- **explanation**: The wrapper itself is a correct MorphismProperty version of the class IsStrictHom. The problem is the class: it requires every square F_i X → X over F_i Y → Y to be a pullback, i.e. F_i X = f⁻¹(F_i Y), so the filtration on X is the inverse image of the one on Y. That is not strictness in the standard (Deligne) sense, f(F_i X) = f(X) ∩ F_i Y. Counterexample in abelian groups with I = {0 ≤ 1}: X = ℤ with F_0 X = 0 ⊂ F_1 X = ℤ, Y = 0, f = 0. Deligne's condition holds trivially (both sides are 0), so f is strict. But the square at i = 0 (0 → ℤ over 0 → 0) is not a pullback, since that pullback is ℤ. So the definition says f is not strict. More generally, the pullback condition forces ker f ⊆ F_i X for all i. It therefore rejects many standard strict morphisms, such as surjections onto a quotient with the quotient filtration. Further evidence: the file proves these morphisms are closed under composition (IsMultiplicative), while Deligne-strict morphisms are well known not to be. The library has formalized the notion of 'cartesian' morphism (inverse-image filtration), not strict morphism.


## Tau Ceti (11 flagged)

### [`spatialFDeriv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Calculus/ParametricFDeriv.lean#L86-L89) — `tauceti-0014`

Snippet: `samples/tauceti/tauceti-0014.lean`

- **verdict**: `too_narrow`
- **intended_object**: The spatial Jacobian of a parametric map F(t, x): for fixed x, the function t ↦ D₂F(t, x), i.e. the partial Fréchet derivative of F in the spatial variable x. It is taken here as the total derivative of F at (t, x) restricted to the E factor, with the documented junk value 0 where F is not jointly differentiable. Inferred from the docstring, the module documentation and the lemmas `hasFDerivAt_timeSlice` and `fderiv_timeSlice`.
- **explanation**: The body is `(fderiv 𝕜 F (t, x)).comp (inr 𝕜 𝕜 E)`, the total derivative restricted to the second factor. Wherever F is differentiable at (t, x) this equals the partial derivative D₂F(t, x), as `fderiv_timeSlice` shows. The value 0 at points where F is not jointly differentiable is stated in the docstring, so I treat it as a deliberate junk-value choice rather than an error, even though the textbook partial derivative also exists at points where only the slice y ↦ F(t, y) is differentiable.

It is too narrow because the parameter space is fixed to the scalar field 𝕜. The construction uses no property of 𝕜 as a parameter space. `fderiv 𝕜 F (p, x) ∘L inr 𝕜 P E` makes sense for F : P × E → F' with P any normed 𝕜-space, and the partial derivative D₂F on a product of normed spaces is the standard notion in the literature. Only the companion definition `timeFDeriv` needs a scalar parameter, because it evaluates at the direction (1, 0); `spatialFDeriv` does not. The library itself shows the restriction matters:
- The module docstring describes maps `F : P × E → F'` with a general parameter space P.
- The main mixed-derivative theorem, `TauCeti.hasFDerivAt_spatialFDeriv`, is stated for a general normed parameter space P. It cannot use `spatialFDeriv` and writes `fun q ↦ fderiv 𝕜 (fun y ↦ F (q, y)) x` by hand instead.

Mathlib has no partial-Fréchet-derivative definition (I found no `partialFDeriv` or similar), so there is no counterpart to cite. Still, the natural generality is a general normed parameter space P, not 𝕜.

### [`LinearMap.BilinForm.dualSubmoduleEquivDual`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/BilinearForm/DualLattice.lean#L79-L87) — `tauceti-0022`

Snippet: `samples/tauceti/tauceti-0022.lean`

- **verdict**: `too_narrow`
- **intended_object**: The perfect-duality isomorphism N^∨ ≅ Hom_R(N, R), where N is a full R-lattice in a finite-dimensional K-vector space V (K = Frac R), B is a nondegenerate bilinear form on V, and N^∨ = {x ∈ V : B(x, N) ⊆ R} is the dual lattice. The map sends x to y ↦ B(x, y). This comes from the docstring and from the TODO on Mathlib's `dualSubmoduleToDual`, which says "Show that this is perfect when `N` is a lattice and `B` is nondegenerate".
- **explanation**: The construction itself is correct. It bundles Mathlib's canonical pairing `B.dualSubmoduleToDual N` with `LinearEquiv.ofBijective`. Injectivity is Mathlib's `dualSubmoduleToDual_injective`, which needs only nondegeneracy and that N spans V. Surjectivity is the library's lemma, which uses an R-basis of N, so the map is the intended one.

The problem is the extra hypothesis `[Module.Free R N]`. The statement holds for every full lattice in Mathlib's sense, `Submodule.IsLattice K` (a finitely generated R-submodule whose K-span is V), with no freeness. Proof sketch: take f : N → R. Because K is the fraction field and N spans V, every v ∈ V has some nonzero d ∈ R with d·v ∈ N. Then f_K(v) := f(d·v)/d is a well-defined K-linear extension of f to V → K. V is finite-dimensional because N is finitely generated and spans V, so nondegeneracy of B gives some x with B(x, ·) = f_K. This x lies in the dual submodule and maps to f. No basis of N is needed.

In the standard setting of lattices over a Dedekind domain (Reiner, Neukirch; fractional ideals, the inverse different), lattices are projective but in general not free. So the freeness assumption excludes cases where the notion is standard and the isomorphism holds. Mathlib's own TODO states the goal for any lattice N, not a free one. Freeness is a proof convenience here (it allows `extendOfIsLattice` and `dualBasis`), not something the object requires. So the definition is correct but stated in narrower generality than its natural one.

### [`TauCeti.D4Tripled.d4BlockTwoToZeroEquiv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/D4/Tripled/BlockIntertwiners.lean#L286-L289) — `tauceti-0044`

Snippet: `samples/tauceti/tauceti-0044.lean`

- **verdict**: `too_narrow`
- **intended_object**: The triality intertwiner from block 2 to block 0 of the tripled D₄ weight table: the linear isomorphism, in coordinates, from the half-spin representation V(ϖ₄) to the vector representation V(ϖ₁). It reindexes coordinates along the order-three triality permutation (inferred from the docstring and the module documentation).
- **mathlib_counterpart**: LinearEquiv.piCongrLeft'
- **explanation**: The body is `LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockTwoToZeroIndexEquiv`, a pure reindexing of coordinate vectors along the bijection `Block 2 ≃ Block 0`. That bijection is the library's `blockIndexEquiv 2` followed by a cast that rewrites `Block (finRotate 3 2)` as `Block 0`. The construction is correct: the library proves the cycle identity and the intertwining of the raising, lowering and Cartan generator matrices. However, nothing in it uses anything about ℚ. `piCongrLeft'` works over any semiring, and the generator matrices are integer matrices that can be cast into any ring. The same file already defines the construction over an arbitrary semiring as `blockModuleEquiv R j`, and its module documentation says each restricted equivalence "induces a linear equivalence over every semiring". This definition copies that construction with the ring fixed to ℚ, adding only the rewrite of the index type `Block (finRotate 3 2)` to `Block 0`, which needs no special property of ℚ. The natural setting is an arbitrary (semi)ring R, with type `(Block 2 → R) ≃ₗ[R] (Block 0 → R)`. Fixing ℚ is an unneeded narrowing of a construction the library itself states in general.

### [`TauCeti.F4ShortRoot.representedChevalleyAlgebra`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/F4/ShortRoot/Represented/Chevalley.lean#L116-L120) — `tauceti-0195`

Snippet: `samples/tauceti/tauceti-0195.lean`

- **verdict**: `incorrect`
- **intended_object**: The type-F₄ Chevalley algebra over R (L_ℤ ⊗ R, with L_ℤ the ℤ-span of a Chevalley basis), realised as its image in 26×26 matrices via the integral 26-dimensional representation. This is inferred from the name, the docstring and the module doc (the "represented F4 Chevalley algebra in characteristic two", whose short-root ideal and quotient are meant to give the special isogeny).
- **explanation**: The body is the range of the Serre-algebra representation over R, i.e. the R-span of iterated brackets of the matrices for the generators e_i, f_i, h_i. Over a field of characteristic 0 this is f₄ in gl₂₆. Over ℤ or ZMod 2 it is only the image of the Lie subring L′ generated by the simple root vectors e_{±αᵢ}, a proper sublattice of the Chevalley lattice for F₄.

Concrete discrepancy: R = ZMod 2 and γ = α₂+2α₃ (α₃ short). (1) The image is graded by weight differences, and its γ-component is spanned by the matrix of [E₃,[E₃,E₂]] ≡ E₃²E₂ + E₂E₃² = 2(D₃E₂ + E₂D₃) ≡ 0 mod 2, using the integral divided square E₃² = 2D₃ proved in Basic.lean. (2) No other path reaches γ: modulo the ideal I of short root vectors and short coroots of the mod-2 Chevalley algebra, the short simple vectors vanish, so the algebra generated by the simple vectors lies, mod I, inside the A₂-part spanned by e_{±α₁}, e_{±α₂}, e_{±(α₁+α₂)}, h₁, h₂, which does not contain the long vector e_γ. (3) The true Chevalley algebra mod 2 contains e_γ, whose matrix in the 26-dim representation is nonzero: it sends the weight vector of −α₃ to ±1 times that of α₂+α₃, since the string has length one.

So over ZMod 2 the definition is missing the long root space e_{α₂+2α₃} and has dimension at most 51, rather than being the 52-dimensional Chevalley algebra (or its image). Its short-root ideal and quotient are then not those needed for the special isogeny. The library defines the genuine mod-2 algebra separately as f4ModularChevalleyLieAlgebra := ZMod 2 ⊗[ℤ] f4ChevalleyLieLattice in ModularLattice.lean.

Caveat: the docstring literally says "the image of the base-changed Serre representation", so the body matches the docstring. The error is in identifying that image with the Chevalley algebra. If only the image was meant and the name is loose, the verdict would change.

### [`SimpleGraph.coarseInducedGraphEstimate3`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Combinatorics/Regularity/Graph/InducedCount.lean#L141-L149) — `tauceti-0282`

Snippet: `samples/tauceti/tauceti-0282.lean`

- **verdict**: `too_narrow`
- **intended_object**: This is the main term of the induced graph counting lemma for a partition P = {V_1,…,V_r} of V(G), taken here for a pattern graph J on three labelled vertices: Σ over injective φ : V(J) → P of ∏_i |φ(i)| · ∏_{i<j} (d(φ i, φ j) if ij ∈ E(J), else 1 − d(φ i, φ j)). It is the prediction of the labelled induced count of J in G. I took this from the docstring, the module doc and the reference to Zhao, Ch. 2.
- **explanation**: The body matches the docstring and the standard formula. It sums over injective assignments `φ : Fin 3 → P.parts`. Each term is the volume `∏ i, #(φ i)` times a product over ordered pairs `i < j`. That factor is the edge density `G.edgeDensity (φ i) (φ j)` when `J.Adj i j` and `1 − density` otherwise, so each unordered pair of J's vertices is counted once. Leaving out non-injective assignments is a stated design choice, and the theorems in the file deal with them separately (the repeated-cell bound). Mathlib's `edgeDensity` is the right density notion, so nothing is mathematically wrong for three-vertex J.

The problem is generality. The construction uses nothing about the number 3. The same formula, with `Fin 3` replaced by `Fin k` or by any finite vertex type of J with a linear order (or a sum over off-diagonal `Sym2` pairs), gives the main term of the induced counting lemma for an arbitrary finite pattern graph H. That is how Zhao's *Graph Theory and Additive Combinatorics*, cited by the file, states the induced counting lemma. Likewise, the companion count `inducedGraphCount3` is just `Fintype.card (J ↪g G)`, which makes sense for any finite J. Restricting the pattern to `Fin 3` fixes one particular index type when any finite index type works, so the definition is too narrow.

Mathlib has no general counterpart; I found no induced-count prediction in Mathlib's regularity or counting files.

### [`TauCeti.spechtModule`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean#L358-L371) — `tauceti-0459`

Snippet: `samples/tauceti/tauceti-0459.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Specht module S^μ of a partition μ ⊢ n: the span of the polytabloids e_t = κ_t{t} inside the Young permutation module M^μ, as a representation of S_n (docstring, module doc, James Ch. 4).
- **explanation**: The construction is correct. It is the span of the column antisymmetrizers b_t = Σ_{q∈C_t} sign(q) q applied to the tabloids {t} inside M^μ, made into a subrepresentation and transported from Perm (Fin |μ|) to Perm (Fin n) along finCongr (a harmless relabeling). However, the base field is hardcoded to ℚ throughout: permutationModule, columnAntisymmetrizer : MonoidAlgebra ℚ _, Submodule.span ℚ, and FDRep ℚ. The construction uses no property of ℚ; the only scalars are 1 and the signs ±1, which exist in any commutative ring. In the literature, the Specht module is standardly defined over an arbitrary field F (James, Def. 4.3), and also over ℤ. Specht modules in positive characteristic are central objects of modular representation theory, and James's submodule theorem holds over any field. The characteristic-0 results the library aims for (irreducibility, the classification) are properties of S^μ, not ingredients of its definition. So the definition should be stated over a general field or commutative ring k. Mathlib has no Specht module to compare with.

### [`TauCeti.semilocalEquiv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Basic.lean#L193-L207) — `tauceti-0533`

Snippet: `samples/tauceti/tauceti-0533.lean`

- **verdict**: `too_narrow`
- **intended_object**: The semi-local decomposition: the canonical isomorphism of K_v-algebras K_v ⊗_K L ≅ ∏_{w | v} L_w, given on pure tensors by a ⊗ x ↦ (a·x)_w, for a finite place v of K and the places w of L above it. Inferred from the docstring, the module documentation (Neukirch II (8.3)), and `semilocalHom`.
- **explanation**: The map is right. `semilocalHom` is `Algebra.TensorProduct.lift` of the structure map K_v → ∏ L_w and the diagonal L → ∏ L_w. Each L_w is a K_v-algebra through the completion map. The index set is the finite places of L lying over v. On pure tensors it sends a ⊗ x to (a·x)_w, and `semilocalEquiv` packages it with its proven bijectivity. So within its stated setting it is the intended isomorphism.

The setting is narrower than the standard one, though. Number-field hypotheses appear only in how bijectivity is proved: weak approximation for number fields, and finiteness of residue fields in the local degree formula. The construction itself uses only `HeightOneSpectrum.adicCompletion`, which Mathlib defines for any Dedekind domain. It also uses the K_v-algebra structure on L_w from the library's own `AdicCompletionExtension` file, which lives under `RingTheory/DedekindDomain`. The textbook statement has the same generality. Serre, *Local Fields*, Ch. II §3, Thm. 1 states it for A a Dedekind domain with fraction field K, L/K finite separable and B the integral closure of A in L: K_𝔭 ⊗_K L ≅ ∏_{𝔓|𝔭} L_𝔓. Neukirch's (8.3) states it for any valued field and any finite separable extension. Number fields automatically give separability (characteristic 0) and the Dedekind structure. The general version would only need an explicit `[Algebra.IsSeparable K L]` and the integral-closure setup, and it would cover function fields as well, which the library also treats.

Mathlib has no general version of this isomorphism. Its archimedean analogue (`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`) is specific to number fields, and so is the library's analogue for infinite places. Even so, the finite-place construction itself makes sense, and is standard, for Dedekind domains with a finite separable extension of fraction fields. That is why I judge it too narrow rather than wrong.

### [`TauCeti.InternalGrading.ofGradedObject`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Module/GradedModule/GradedObject.lean#L122-L130) — `tauceti-0564`

Snippet: `samples/tauceti/tauceti-0564.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical internal grading on the external direct sum ⨁ₚ Xₚ of a graded family of R-modules: the degree-p piece is the image of the canonical inclusion Xₚ → ⨁_q X_q. This comes from the docstring and the module documentation.
- **explanation**: The definition is mathematically correct. The pieces are `LinearMap.range (DirectSum.lof R ℤ X p)`. The proof that these form an internal direct sum identifies `coeLinearMap` with the inverse of the componentwise equivalence `X p ≃ range (lof p)`, so the canonical copies of the components are exactly the homogeneous pieces of ⨁ X. This is the standard internal grading of an external direct sum.

However, nothing in the construction uses the index type ℤ. `DirectSum.lof`, `DirectSum.of_injective`, `LinearEquiv.ofInjective`, `DirectSum.congrLinearEquiv`, `DirectSum.coeLinearMap` and `DirectSum.linearMap_ext` all work for an arbitrary index type ι with `DecidableEq ι`. The library's own structure `InternalGrading (R M) (ι : Type := ℤ) [DecidableEq ι]` is parametrized by an arbitrary index type; ℤ is only the default. Mathlib's `CategoryTheory.GradedObject β C` is also stated for an arbitrary β. So the canonical grading on the external direct sum of a family indexed by ι makes sense, word for word, for any ι with decidable equality. Fixing ι = ℤ specializes the index type when any index type works, so the definition is too narrow. The ℤ restriction reflects the library's DGA roadmap, not the content of the construction. I found no Mathlib declaration that packages exactly this internal grading on ⨁ X.

### [`TauCeti.Place.decompositionQuotientInertiaEquiv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/FieldTheory/FunctionField/Place/Extension/Inertia.lean#L306-L311) — `tauceti-0737`

Snippet: `samples/tauceti/tauceti-0737.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical isomorphism G_Z(P)/G_T(P) ≅ Aut(F'_P / F_{P∩F}) between the decomposition group modulo the inertia group of a place in a finite Galois extension F'/F and the automorphism group of the residue field extension, induced by the residue action (from the docstring and module doc, Stichtenoth Thm 3.8.2).
- **mathlib_counterpart**: Ideal.Quotient.stabilizerQuotientInertiaEquiv
- **explanation**: The definition is QuotientGroup.liftEquiv applied to residueAut: the action of the decomposition group on the residue field, by automorphisms over the residue field below. It uses the library's proofs that residueAut is surjective and that its kernel is the inertia group. The map is the correct one, and the companion lemma `_mk` checks that it is induced by the residue action. However, `Place k F'` here is a normalized ℤᵐ⁰-valued (discrete rank-one) valuation trivial on k. Every ingredient of the statement exists for an arbitrary valuation subring A of L with L/K finite Galois. The groups used, `P.integers.decompositionSubgroup F` and `P.integers.inertiaSubgroup F`, are Mathlib's `ValuationSubring` notions, defined at that generality. The residue field below is just the residue field of the pulled-back valuation ring. Surjectivity of D → Aut(κ_A/κ_{A∩K}) is a classical theorem for arbitrary valuation rings in finite Galois extensions; it does not need discreteness, normalization, or the field k. Mathlib also already provides this isomorphism for any finite-group invariant extension of rings: `Ideal.Quotient.stabilizerQuotientInertiaEquiv`. It specializes to this one by taking B to be the integral closure of the valuation ring below in F' and Q = m_P ∩ B, since 𝒪_P is the localization of B at Q. So the construction is correct but stated only for discrete places of the library's framework, rather than for arbitrary valuation subrings (or invariant ring extensions), which is its natural generality and the one Mathlib uses for comparable notions.

### [`TauCeti.Lie.tangentAd`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Lie/Adjoint/Basic.lean#L273-L284) — `tauceti-0788`

Snippet: `samples/tauceti/tauceti-0788.lean`

- **verdict**: `too_narrow`
- **intended_object**: The adjoint representation of a Lie group G at an element g, inferred from the docstring, name and module doc. Ad(g) = d(c_g)_1, the differential at the identity of conjugation x ↦ g x g⁻¹, viewed as a Lie algebra automorphism of Lie(G) = T₁G.
- **explanation**: The construction is mathematically correct. `conjDiffeomorph g` is x ↦ g*x*g⁻¹. `adjointContinuousLinearEquiv g` is its mfderiv at 1, packaged as a continuous linear equivalence on `GroupLieAlgebra I G` (the tangent space at 1). `tangentAd` reuses this linear equivalence and gets bracket preservation from `adjointContinuousLinearMap_lie`, which is proved by naturality of the manifold Lie bracket under pullback. So `tangentAd g` is exactly Ad(g) as a Lie algebra automorphism, and `tangentAd_one` and `tangentAd_mul` hold. The hypotheses `CompleteSpace E` and C³ smoothness are just what Mathlib needs for the Lie bracket on `GroupLieAlgebra`.

However, the definition is fixed to the scalar field ℝ (`NormedSpace ℝ E`, `ModelWithCorners ℝ E H`, `LieGroup I 3 G`). Mathlib's `GroupLieAlgebra I G`, its `LieRing` instance and `instLieAlgebraGroupLieAlgebra : LieAlgebra 𝕜 (GroupLieAlgebra I G)` are defined over any `NontriviallyNormedField 𝕜`, assuming `[LieGroup I (minSmoothness 𝕜 3) G]` and `[CompleteSpace E]`. The library's own `conjDiffeomorph` and `conj` (in `Adjoint/Conjugation.lean`) are also stated over a general 𝕜. Every ingredient also works over a general 𝕜: `Diffeomorph.mfderivToContinuousLinearEquiv`, `VectorField.mpullback_mlieBracket` and `mulInvariantVectorField`. ℝ is used only to turn `minSmoothness ℝ 3` into 3, through `LieGroup.minSmoothnessThree`. The same definition therefore makes sense, as a 𝕜-linear Lie algebra equivalence, for complex Lie groups (where Ad is complex-linear, which the ℝ version cannot express) and for analytic Lie groups over other fields. That is the generality in which Mathlib sets up the group Lie algebra. Mathlib itself has no adjoint representation on `GroupLieAlgebra`, so there is no direct counterpart to cite.

### [`TauCeti.koszulBraiding`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/Monoidal/Braiding.lean#L378-L384) — `tauceti-0947`

Snippet: `samples/tauceti/tauceti-0947.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Koszul (signed) symmetry isomorphism X ⊗ Y ≅ Y ⊗ X of cochain complexes for the totalized tensor product. On the summand X^p ⊗ Y^q it is (-1)^{pq} times the braiding of the base category, i.e. x ⊗ y ↦ (-1)^{|x||y|} y ⊗ x. This comes from the docstring, the module documentation and its use as the `braiding` of `koszulBraidedCategory`.
- **explanation**: As a definition of the Koszul braiding for ℤ-graded cochain complexes of R-modules, it is correct. `koszulBraidingSummand` is (p*q).negOnePow • (β_ (X.X p) (Y.X q)).hom followed by the inclusion of the (q,p) summand of Y ⊗ X. `koszulBraidingHom` assembles these summands with `mapBifunctorDesc`. The inverse is the same construction with X and Y swapped, which is right because ModuleCat R is symmetric and the sign (-1)^{pq} is symmetric. The sign convention matches Mathlib's tensor signs for `ComplexShape.up ℤ` (ε₁ = 1, ε₂(p,q) = (-1)^p). It also agrees with Mathlib's own `TotalComplexShapeSymmetry (up ℤ) (up ℤ) (up ℤ)` instance, where σ p q = (p*q).negOnePow.

The setting is narrower than the construction needs. The body only uses:
- a braided (for the inverse to be the swapped braiding, symmetric) monoidal structure on the base category;
- composition being ℤ-linear, used to scale by units of ℤ;
- the totalized tensor product, the inclusions ιMapBifunctor and mapBifunctorDesc;
- a sign σ satisfying the Leibniz compatibilities.

Nothing about modules, or about the ring R, is used. Mathlib's `HomologicalComplex.monoidalCategory` is stated for an arbitrary preadditive monoidal category C and any complex shape with `TensorSigns`. Mathlib also already has the general sign class `TotalComplexShapeSymmetry` with its `σ`, and the general flip isomorphism `HomologicalComplex.mapBifunctorFlipIso`. Composing that flip isomorphism (with F = curriedTensor C) with the braiding of C gives exactly this Koszul braiding, for any braided monoidal preadditive C with the needed coproducts, and for any shape such as `up ℤ` or `down ℕ`. The literature also states it at that level: Ch(A) is symmetric monoidal for a symmetric monoidal additive category A.

So the definition is the special case C = ModuleCat R, c = up ℤ of a construction that makes sense, and is standard, for cochain complexes in any symmetric (or braided) monoidal preadditive category, and more generally over any complex shape with `TotalComplexShapeSymmetry`. Mathlib has no ready-made braiding on `HomologicalComplex` to cite, only the building block `HomologicalComplex.mapBifunctorFlipIso`.


## Lean Pool (33 flagged)

### [`CKN.Foundation.Euclidean.lpPairingWith`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/LpExtension.lean#L468-L474) — `lean-pool-0041`

Snippet: `samples/lean-pool/lean-pool-0041.lean`

- **verdict**: `too_narrow`
- **intended_object**: For a fixed g ∈ L^q, the continuous linear functional f ↦ ∫ f g on L^p, with p and q Hölder conjugates. This is the canonical map from L^q into the dual of L^p. Inferred from the docstring and from the lemma `lpPairingWith_apply` (`= ∫ x, f x * g x`).
- **mathlib_counterpart**: ContinuousLinearMap.lpPairing
- **explanation**: The definition is correct. It takes Mathlib's `ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ)`, which by `lpPairing_eq_integral` is f ↦ g ↦ ∫ f(x) g(x) dx, and evaluates it at the fixed g using `ContinuousLinearMap.apply`. The result is the functional f ↦ ∫ f g, as the docstring says.

The problem is the setting. The definition is fixed to `Vec3` (ℝ³) with Lebesgue measure `volume`, but nothing in the body uses that setting. Mathlib's `lpPairing` works for any measure space (α, μ), with any Hölder-conjugate exponents and any continuous bilinear map B : E →L F →L G.

The Hölder pairing against a fixed function in the conjugate space is standard on an arbitrary measure space. Here it is just Mathlib's general construction written out for ℝ³ with Lebesgue measure. A general version would take a measure μ on any measurable space, and perhaps a general scalar field 𝕜 or a bilinear map B. So the definition is too narrow, and its general counterpart is `ContinuousLinearMap.lpPairing`.

### [`quadForm`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OSforGFF/Bochner/Sazonov.lean#L62-L63) — `lean-pool-0094`

Snippet: `samples/lean-pool/lean-pool-0094.lean`

- **verdict**: `too_narrow`
- **intended_object**: The quadratic form x ↦ ⟪x, Sx⟫ of a bounded operator S on a real inner product space (from the docstring). In the module it is used for positive operators in the proof of Sazonov's theorem.
- **mathlib_counterpart**: ContinuousLinearMap.reApplyInnerSelf
- **explanation**: The body, `inner x (S x)`, does compute ⟪x, Sx⟫ correctly. But because of the section `variable` line, the definition also carries `[CompleteSpace H]` as an instance argument. Lean 4 automatically includes an instance-implicit variable once all the types it mentions are included, and this one mentions only `H`. The construction never uses completeness: it only needs a real inner product space, and the continuity of S comes from the type `H →L[ℝ] H`.

Mathlib already provides this construction in general. `ContinuousLinearMap.reApplyInnerSelf` (in Mathlib/Analysis/InnerProductSpace/LinearMap.lean) is defined as `re ⟪T x, x⟫` for any continuous linear endomorphism of an inner product space over an `RCLike` field 𝕜, with no completeness assumption. Over ℝ, `re` is the identity and the inner product is symmetric, so `reApplyInnerSelf S x = ⟪S x, x⟫ = ⟪x, S x⟫ = quadForm S x`. Mathlib also states `IsPositive` in terms of `reApplyInnerSelf`.

So `quadForm` is a re-implementation of a Mathlib construction, restricted to ℝ and to complete spaces. The definition's own content needs neither restriction; completeness only matters for later results in the file about Sazonov's theorem.

### [`EulerMeanCoefficients.translated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanCoefficientSpatial.lean#L31-L33) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- **verdict**: `too_narrow`
- **intended_object**: The translation operator on bounded continuous functions: for a bounded continuous field A on physical space and a vector a, the translate x ↦ A(x + a), again a bounded continuous function. Inferred from the name, the docstring and the body.
- **explanation**: Here `Space` is `EuclideanSpace ℝ (Fin 3)` (from `Euler/Foundations/DifferentialOperators.lean`). The body is `A.compContinuous ⟨fun x => x + a, _⟩`, so `translated A a x = A (x + a)`. That is the correct translate, and it is bounded and continuous as required. So the definition is mathematically right.

The only fact about `Space` it uses is that `x ↦ x + a` is continuous. Precomposing with a continuous map always gives a bounded continuous function, so the same construction works on any topological space with a continuous addition (`[Add X] [ContinuousAdd X]`, or any topological additive group). Translation of functions is a standard operation on topological groups, and nothing here uses the Euclidean structure, the dimension 3 or the inner product.

The codomain `V` is already left general, which makes it clearer that fixing the domain to ℝ³ is a needless restriction and not part of what the definition needs. Mathlib has no dedicated named translation operator for `→ᵇ`. The general tool is `BoundedContinuousFunction.compContinuous`, and this definition just applies it in one specific space. This matches the "notion defined on ℝ^d that makes sense in any (topological) additive group" pattern, so the verdict is too_narrow and not incorrect.

### [`GapCVP.Core.rootSupportPolynomial`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/GapCVP/Part09.lean#L1014-L1017) — `lean-pool-0116`

Snippet: `samples/lean-pool/lean-pool-0116.lean`

- **verdict**: `too_narrow`
- **intended_object**: The monic polynomial whose roots are a given family r_0,…,r_{h-1} (counted with multiplicity), ∏_i (X − r_i). This is what the body computes, and the library's lemmas about it (monic, natDegree = h, each r_i is a root, a moment recurrence) confirm it. The docstring ("GapCVP reduction support") says nothing useful.
- **mathlib_counterpart**: Lagrange.nodal
- **explanation**: The body is exactly ∏ i : Fin h, (X − C (roots i)), so it is mathematically correct for the intended object. However, nothing in it uses division or any other field structure. The product of linear factors X − C r makes sense in R[X] for any commutative ring R, and over any finite index set, not just Fin h. Mathlib already provides this construction in that generality: `Lagrange.nodal (s : Finset ι) (v : ι → R) : R[X] := ∏ i ∈ s, (X - C (v i))`, with R a commutative ring. Here `rootSupportPolynomial roots` is literally `Lagrange.nodal Finset.univ roots`. The library's own lemmas also hold over any commutative ring: monicity comes from `Polynomial.monic_prod_X_sub_C`, the degree is h, and each r_i evaluates to 0. Since the definition rewrites a general Mathlib construction in a special setting (fields, Fin h) that its content does not need, it is too narrow.

### [`ConnesRigidity.crossedFiberwiseOperator`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InfiniteConnesRigidity/CarryAndCrossedProduct.lean#L7009-L7040) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- **verdict**: `too_narrow`
- **intended_object**: The ampliation (diagonal amplification) T ⊗ 1 of a bounded operator T on H, acting coordinatewise on ℓ²(K, H) ≅ ℓ²(K) ⊗ H by (ξ_k)_k ↦ (T ξ_k)_k. This is inferred from the name, the body, and how it is used: `crossedFiberwiseOperator_apply` and the commutant lemmas in SpectralAndPropertyT.lean.
- **mathlib_counterpart**: lp.mapCLM
- **explanation**: The definition is mathematically correct. It sends ξ to k ↦ T(ξ k), the result lies in ℓ², and the operator norm is bounded by ‖T‖. So it does define the ampliation T ⊗ 1 on ℓ²(K, H).

The setting is narrower than the construction needs:
- K carries a `[Group K]` instance, picked up from the section variables, but the body never uses the group structure. Any index type works.
- The construction does not depend on the field ℂ or on the exponent 2. It works over any (nontrivially) normed field and for any ℓ^p with 1 ≤ p.

Mathlib already has this construction in general. `lp.mapCLM` (Mathlib/Analysis/Normed/Lp/lpHolder.lean) turns any uniformly bounded family T_i : E i →L[𝕜] F i into a continuous linear map lp E p →L[𝕜] lp F p. The present definition is exactly `lp.mapCLM 2 (fun _ ↦ T) (norm_nonneg T) (fun _ ↦ le_rfl)`, restricted to a constant family, p = 2, 𝕜 = ℂ and a group as index type. Its body re-proves the same membership and norm bound that `lp.mapCLM` packages.

Since the definition hand-writes, in a special setting, a construction Mathlib provides in general, and none of the special hypotheses are used, it is too narrow.

### [`RS.symplecticJ`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Novel/Skein/SuperSpace.lean#L38-L44) — `lean-pool-0230`

Snippet: `samples/lean-pool/lean-pool-0230.lean`

- **verdict**: `too_narrow`
- **intended_object**: The standard symplectic matrix J = [[0, I_ℓ], [-I_ℓ, 0]] of size 2ℓ, i.e. the Gram matrix of the standard skew-symmetric form xᵀJy. This comes from the docstring and the module documentation.
- **mathlib_counterpart**: Matrix.J
- **explanation**: The definition gives the intended matrix. With 0-based indices on Fin (2ℓ), the entry at (c, c+ℓ) is 1, which is the identity block in the top right. The entry at (d+ℓ, d) is -1, which is the -I block in the bottom left. Every other entry is 0. Degenerate cases are also fine: for ℓ = 0 the matrix is empty.

The body uses only the constants 0, 1 and -1. So the same matrix makes sense over any ring, and in particular over any commutative ring, which is the standard setting for symplectic matrices. Fixing the scalars to ℂ is not needed by anything in the construction.

Mathlib already has this object in general: `Matrix.J l R : Matrix (l ⊕ l) (l ⊕ l) R`, defined as `fromBlocks 0 (-1) 1 0` over an arbitrary commutative ring R, in `Mathlib/LinearAlgebra/SymplecticGroup.lean`. Mathlib's matrix uses the opposite sign convention. The matrix here equals `-(Matrix.J (Fin ℓ) ℂ)` (equivalently its transpose), reindexed along `Fin ℓ ⊕ Fin ℓ ≃ Fin (2ℓ)`.

This definition writes out a construction Mathlib provides in general, and it does so for one specific ring (ℂ) and one specific index type (Fin (2ℓ)) when any commutative ring and any index type would work. That makes it faithful in content but narrower than the natural generality.

### [`Malliavin.dualLp`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/DualDerivative.lean#L195-L197) — `lean-pool-0262`

Snippet: `samples/lean-pool/lean-pool-0262.lean`

- **verdict**: `too_narrow`
- **intended_object**: The L² class of a continuous linear functional L, i.e. the element of L²(μ) given by x ↦ L(x), here for a Gaussian measure μ on a Banach space. Inferred from the docstring and the name.
- **mathlib_counterpart**: StrongDual.toLp
- **explanation**: The body is correct: `IsGaussian.memLp_dual` shows that L is in Lᵖ(μ) for every finite p, and `MemLp.toLp` takes the a.e.-class of L in L²(μ). So the definition does give the L² class of L.

It is narrower than it needs to be, though. The only thing the Gaussian assumption does here is supply the proof that L is square-integrable. The construction "send a continuous linear functional to its class in Lᵖ(μ)" makes sense for any measure with a p-th moment (`MemLp id p μ`), over any normed field 𝕜. Mathlib already has it in that generality:
- `StrongDual.toLpₗ μ p` is a linear map.
- `StrongDual.toLp μ p` is a continuous linear map from `StrongDual 𝕜 E` to `Lp 𝕜 p μ`, defined on any normed space E.
- Both take the junk value 0 when `MemLp id p μ` fails.
- `StrongDual.toLp_apply` states `L.toLp μ p = MemLp.toLp L _` whenever `MemLp id p μ` holds, which is exactly this body.

By Fernique's theorem a Gaussian measure has a second moment, so `Malliavin.dualLp μ L` is `StrongDual.toLp μ 2 L` written out again in the special case p = 2, 𝕜 = ℝ, μ Gaussian. On top of that, the section variables add `CompleteSpace W` and `SecondCountableTopology W`, which the construction never uses.

So the definition rewrites, in one particular setting, a construction that Mathlib provides in general, and its content does not need that setting.

### [`EulerBoundedFieldCalculus.multilinearAlgebra`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/SmoothTimeFieldComposition.lean#L183-L211) — `lean-pool-0293`

Snippet: `samples/lean-pool/lean-pool-0293.lean`

- **verdict**: `too_narrow`
- **intended_object**: Given a continuous multilinear map L : ∏ V_i → W, the multilinear map that applies L pointwise to bounded continuous functions: (f_i)_i ↦ (x ↦ L(f_1 x, …, f_n x)), from ∏ (α →ᵇ V_i) to α →ᵇ W. Inferred from the body, the module comment ("A continuous multilinear operation acts on genuine bounded fields in the uniform norm") and its use in `multilinearMap`. It is the multilinear analogue of Mathlib's `ContinuousLinearMap.compLeftContinuousBounded`.
- **mathlib_counterpart**: ContinuousLinearMap.compLeftContinuousBounded
- **explanation**: The definition is correct. Its underlying function is `multilinearValue L`, which sends f to x ↦ L(fun i => f i x). A bound of ‖L‖·∏‖f_i‖ makes this a bounded continuous function. Multilinearity is proved pointwise from L.map_update_add and L.map_update_smul. So it is exactly the pointwise multilinear operator induced by L.

However, it is stated only over the scalar field ℝ, and nothing in the construction uses ℝ. It needs only the scalar action on α →ᵇ V_i and α →ᵇ W, which Mathlib provides for normed spaces over any normed field 𝕜. It also needs only pointwise multilinearity of L, plus the operator-norm bound used by the companion `multilinearValue`/`multilinearMap`; both hold for ContinuousMultilinearMap over any (nontrivially) normed field.

Mathlib's linear analogue, `ContinuousLinearMap.compLeftContinuousBounded`, is stated over a general normed field 𝕜. The natural generality is therefore a general (nontrivially) normed field 𝕜 rather than ℝ. Mathlib has no multilinear version, so the counterpart given is the closest analogue, not the same object.

This definition is also partly a technical stepping stone: it is the algebraic multilinear map that `multilinearMap` turns into a continuous one with `mkContinuous`. It still names a genuine mathematical operator, and the restriction to ℝ is unnecessary for its content.

### [`EulerPhysicalL2Scaling.derivativeSum`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketFieldPhysicalSobolev.lean#L33-L36) — `lean-pool-0301`

Snippet: `samples/lean-pool/lean-pool-0301.lean`

- **verdict**: `too_narrow`
- **intended_object**: The integer-order inhomogeneous Sobolev H^m norm (ℓ¹-type): ‖f‖_{H^m} = Σ_{n=0}^{m} ‖Dⁿf‖_{L²}, where Dⁿf is the n-th Fréchet derivative in operator norm. Inferred from the docstring, from its use in the Euler PhysicalL2Scaling/Sobolev files, and from the lemma `tensorNorm_eq_derivativeSum`.
- **explanation**: The body sums `lpNorm (iteratedFDeriv ℝ n f) 2 volume` for n = 0..m. That is exactly the stated Sobolev H^m norm, and it agrees with the library's own `realTensorSobolevNorm`. Outside L² or smoothness, the value falls back on Mathlib's usual junk conventions, which is acceptable. The problem is the domain: it is fixed to `Space := EuclideanSpace ℝ (Fin 3)`, while the value space `V` is general. The body only uses a real normed-space structure on the domain (for `iteratedFDeriv ℝ`) and a measure (for `volume`). Nothing about dimension 3 or Euclidean structure is used, so the same definition compiles verbatim for any `{E} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]`, e.g. ℝ^d or any finite-dimensional inner product space with its volume measure. The H^m norm is standard on ℝ^d for every d, and Mathlib's comparable Sobolev notion (`TemperedDistribution.MemSobolev`) is stated over any finite-dimensional real inner product space. Fixing d = 3 is therefore an unnecessary specialisation; the Euler application on ℝ³ explains where it is used but does not require the definition to be specialised. Mathlib has no function giving this derivative-based norm. `MemSobolev` is only a related membership predicate, defined through the Bessel potential and the Fourier transform, so no exact counterpart is cited.

### [`LeanCert.Engine.matrixCLM`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/Development/IntervalArithmetic/Foundations/Development002.lean#L4988-L4991) — `lean-pool-0320`

Snippet: `samples/lean-pool/lean-pool-0320.lean`

- **verdict**: `too_narrow`
- **intended_object**: The continuous linear map v ↦ A·v given by a matrix A, acting on coordinate vectors (from the docstring "Interpret a real matrix as a continuous linear map on finite coordinate vectors" and the name).
- **mathlib_counterpart**: LinearMap.toContinuousLinearMap
- **explanation**: The body is `ContinuousLinearMap.mk (Matrix.mulVecLin A)`, which correctly gives the continuous linear map v ↦ A *ᵥ v; continuity is discharged automatically. However, it is restricted to square real matrices indexed by `Fin n`. The construction needs none of these restrictions. Matrix-vector multiplication is linear for any m×n matrix over a semiring. It is continuous whenever the column index type is finite and the scalars form a topological semiring. Mathlib also turns linear maps on finite-dimensional spaces over any complete normed field into continuous linear maps. Mathlib already provides the same object as `LinearMap.toContinuousLinearMap (Matrix.toLin' A)` (and `Matrix.toEuclideanCLM` on EuclideanSpace). So this definition re-implements a general Mathlib construction in one special setting (ℝ, square, `Fin n`) that its content does not need, which makes it too narrow.

### [`RS.SuperCommAlgebra.Mod.tensorIso`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/GammaPairNat.lean#L166-L176) — `lean-pool-0336`

Snippet: `samples/lean-pool/lean-pool-0336.lean`

- **verdict**: `too_narrow`
- **intended_object**: The tensor product of two isomorphisms in the (monoidal) category of super modules over a super-commutative algebra: from P ≅ P' and Q ≅ Q', the isomorphism P ⊗ Q ≅ P' ⊗ Q' with forward map a.hom ⊗ b.hom and inverse a.inv ⊗ b.inv (from the docstring and name).
- **mathlib_counterpart**: CategoryTheory.MonoidalCategory.tensorIso
- **explanation**: The definition is correct. Its forward map is tensorHom a.hom b.hom and its inverse is tensorHom a.inv b.inv; both round-trip equations follow from the facts that tensorHom respects composition and identities. However, the construction only uses the functoriality of the tensor product on morphisms, so it makes sense in any monoidal category. Mathlib provides exactly this as CategoryTheory.MonoidalCategory.tensorIso. The library itself registers `instMonoidalCategory : MonoidalCategory S.Mod.{u,u,u,u}` in SuperModMonoidal.lean (line 2330). That instance sets the tensor of objects to `M.tensor N` and the tensor of morphisms to `SuperCommAlgebra.Mod.tensorHom f g`, and its universe levels fit the ones used here. So `MonoidalCategory.tensorIso a b` applies directly and should be definitionally equal to this definition. This is a re-implementation, in one particular category, of a construction Mathlib has in general, and nothing in it needs the super-module setting.

### [`Schoenflies.poly`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Schoenflies/PolyPath.lean#L43-L48) — `lean-pool-0339`

Snippet: `samples/lean-pool/lean-pool-0339.lean`

- **verdict**: `too_narrow`
- **intended_object**: The carrier (image) of a polygonal path or polygonal chain with vertex list v₀,…,vₙ: the union of the closed segments [vᵢ, vᵢ₊₁]. One vertex gives {v} and the empty list gives ∅. Inferred from the docstring and the module documentation.
- **explanation**: The recursion is correct: poly [v₀,…,vₙ] = ⋃ᵢ segment ℝ vᵢ vᵢ₊₁, poly [v] = {v} and poly [] = ∅, which matches the docstring. However, it is stated only for Plane = EuclideanSpace ℝ (Fin 2). The body uses nothing but `segment ℝ u v`, which exists in any real vector space (indeed in any module over an ordered semiring). It uses neither two-dimensionality, nor the inner product, nor the norm, nor the topology. Polygonal paths and their carriers are standard in any real vector space; for example, open connected subsets of a normed space are polygonally connected, which is the module's own Lemma 1.1, and that lemma does not need the plane either. The planar setting matters only for later Schoenflies-specific results, not for this construction. The natural definition would be `poly : List E → Set E` for `[AddCommGroup E] [Module ℝ E]`. Mathlib has no polygonal-path notion (a grep for "polygonal" finds nothing), so there is no counterpart to cite.

### [`Matrix.unitaryGroup.conj`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/InnerAut.lean#L676-L680) — `lean-pool-0354`

Snippet: `samples/lean-pool/lean-pool-0354.lean`

- **verdict**: `too_narrow`
- **intended_object**: The entrywise complex conjugate Ū of a unitary matrix U, viewed as an element of the unitary group U(n) again (map U ↦ Ū on the unitary group). Inferred from the docstring and the name.
- **mathlib_counterpart**: Matrix.unitaryGroup.map_star
- **explanation**: The body is correct. It takes the matrix `(U)ᴴᵀ`, which is `Matrix.conj`, defined as the transpose of the conjugate transpose, i.e. entrywise `star`. It packages that matrix with a proof that it is unitary, so it gives the intended map U ↦ Ū.

But the hypotheses are narrower than needed. The library assumes `[RCLike 𝕜]`, while the construction works for any commutative star ring. In a commutative ring, `star` is a ring homomorphism, so Ū·(Ū)ᴴ is the conjugate of U·Uᴴ = 1, which is 1. This is the generality in which Mathlib defines `Matrix.unitaryGroup`, namely `[CommRing α] [StarRing α]`.

Mathlib already provides exactly this map in that generality: `Matrix.unitaryGroup.map_star (U : unitaryGroup n α) : unitaryGroup n α := ⟨(U : Matrix n n α).map star, …⟩`, which has the same underlying matrix. Nothing in the definition uses the analytic structure of `RCLike`, so it is a special case of an existing, more general Mathlib definition.

### [`CKN.Leray.allDerivativeScalarVectorActionLinear`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMollifierAllDerivatives.lean#L30-L38) — `lean-pool-0377`

Snippet: `samples/lean-pool/lean-pool-0377.lean`

- **verdict**: `too_narrow`
- **intended_object**: Scalar multiplication (c, x) ↦ c • x viewed as an ℝ-bilinear map ℝ × V → V, here for V = L2Vec3 = PiLp 2 (Fin 3 → ℝ), i.e. Euclidean ℝ³ (from the docstring, the name and its use as the bilinear map of a convolution).
- **mathlib_counterpart**: LinearMap.lsmul
- **explanation**: The body is `LinearMap.mk₂ ℝ (fun c x => c • x)`, with the axioms add_smul, mul_smul, smul_add and smul_comm. This is correct as scalar multiplication packaged as a bilinear map. However, the body uses nothing about L2Vec3: it only needs a module over a commutative semiring. Mathlib's `LinearMap.lsmul R M : R →ₗ[R] M →ₗ[R] M` (Mathlib/LinearAlgebra/BilinearMap.lean) is exactly `mk₂ R (· • ·)` with the same axioms, so `LinearMap.lsmul ℝ L2Vec3` is the same map as this definition. `ContinuousLinearMap.lsmul` gives the continuous version that the library builds next with `mkContinuous₂ 1`. Since the definition writes out a general Mathlib construction for one specific space, it is too narrow.

### [`LStar`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/FormalLearningTheory/Process.lean#L46-L56) — `lean-pool-0409`

Snippet: `samples/lean-pool/lean-pool-0409.lean`

- **verdict**: `incorrect`
- **intended_object**: Angluin's L* algorithm (1987): a specific procedure that, given a minimally adequate teacher (membership and equivalence oracles) for a regular language, keeps a closed and consistent observation table and outputs the minimal DFA for the target language after polynomially many queries. Source: the docstring.
- **explanation**: The structure has only three fields: an arbitrary `MinimallyAdequateTeacher`, an arbitrary natural number `numStates`, and an arbitrary `Option (DFA' Sym (Fin (numStates+1)))`. Nothing ties these fields together. No observation table is stored; the comment admits it is left out. There is no closedness or consistency condition, no update rule driven by membership or equivalence queries, no requirement that `result` accept the teacher's target language or be minimal, and no termination or polynomial query bound. So any triple is an `LStar`. For example, take any teacher with `numStates = 0` and `result = none`. Another instance pairs a teacher whose target is "all words" with a one-state DFA that accepts nothing. Both are valid instances, yet neither has anything to do with what L* computes. The definition therefore does not capture the algorithm its docstring describes. It is just an unconstrained record of a teacher, a number and an optional DFA, so it does not formalize the intended object. Mathlib has no L* or query-learning counterpart.

### [`Stafford38.Characteristic.ArtinianEquation33TraceProducer.IsStrictUpperTriangularOver`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Stafford38/Stafford38/Characteristic/ArtinianEquation33TraceProducer.lean#L55-L58) — `lean-pool-0414`

Snippet: `samples/lean-pool/lean-pool-0414.lean`

- **verdict**: `too_narrow`
- **intended_object**: A strictly upper triangular square matrix: M i j = 0 whenever j ≤ i, i.e. the diagonal and everything below it is zero. Inferred from the docstring and the name.
- **explanation**: The condition `∀ i j, j ≤ i → M i j = 0` is exactly the definition of a strictly upper triangular matrix, so the content is correct. The coefficient type is already general: it only needs `[Zero S]`.

The index type, however, is fixed to `Fin (n + 1)`. That rules out the empty 0×0 case, which is still a valid instance of the notion. More importantly, the body uses nothing about `Fin (n + 1)` except its order `≤`. The same definition makes sense for matrices indexed by any type with an order (`[LE m]`, or a linear order). Mathlib defines the closely related notions in that generality: `Matrix.IsUpperTriangular` takes `[LT m]`, and `Matrix.BlockTriangular` works for an arbitrary `b : m → α` with `[LT α]`. A strict variant would naturally be `∀ i j, j ≤ i → M i j = 0` for `[LE m]`, or `M.BlockTriangular` with respect to a non-strict order. This is the "Fin n when any (ordered) index type works" situation, so the definition is correct but too narrow.

Mathlib has no definition of strictly upper triangular matrices. The closest declaration is `Matrix.IsUpperTriangular`, which is the non-strict version, so `mathlib_counterpart` is left empty.

### [`funTensorProductAssocHasCoe'`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/Ips/Strict.lean#L103-L106) — `lean-pool-0441`

Snippet: `samples/lean-pool/lean-pool-0441.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ExponentialJuliaSetMisiurewicz.IsDevaneyChaotic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ExpChaotic/Dynamics.lean#L192-L195) — `lean-pool-0473`

Snippet: `samples/lean-pool/lean-pool-0473.lean`

- **verdict**: `too_narrow`
- **intended_object**: Devaney chaos for a self-map f of a space X: f is continuous, its periodic points are dense, and it is topologically transitive. Sensitive dependence on initial conditions follows from the other two conditions on infinite metric spaces (Banks et al.). Inferred from the docstring and the name; the library uses it to state Misiurewicz's theorem that exp is chaotic on ℂ.
- **explanation**: The body is correct for ℂ:
- `Continuous f` is continuity.
- `Dense (periodicPts f)` says the periodic points are dense.
- `MulAction.IsTopologicallyTransitive (IterateMulAct f) ℂ` unfolds to: for all nonempty open U and V there is an n with f^[n](U) ∩ V ≠ ∅. That is the usual topological transitivity.

Devaney's original definition also asks for sensitive dependence on initial conditions. Leaving it out is fine here: ℂ is an infinite metric space, and there sensitivity follows from transitivity together with dense periodic points (Banks–Brooks–Cairns–Davis–Stacey).

The problem is generality. Nothing in the body uses the structure of ℂ. Each ingredient (`Continuous`, `Dense`, `Function.periodicPts`, `IterateMulAct`, `IsTopologicallyTransitive`) only needs a topological space. Devaney chaos is standardly defined for a continuous self-map of a metric or topological space. The topological version uses exactly these three conditions; the metric version may add sensitivity, which is redundant on infinite metric spaces.

So the definition could be stated for `f : X → X` with `[TopologicalSpace X]`, or `[MetricSpace X]`, and then applied to `X = ℂ`. The fact that the project only needs exp on ℂ does not make the concept depend on ℂ. Mathlib has no definition of Devaney chaos, but it does provide topological transitivity for any monoid action on a topological space, which shows the natural generality of the ingredients.

### [`EulerMeanVectorIdentities.laplacianTest`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanVectorIdentities.lean#L96-L100) — `lean-pool-0507`

Snippet: `samples/lean-pool/lean-pool-0507.lean`

- **verdict**: `too_narrow`
- **intended_object**: The vector Laplacian as an operator on test fields, f ↦ Δf from C_c^∞(ℝ³, ℝ³) to itself. Inferred from the docstring, the name and the definition of `Test` as the subspace of smooth, compactly supported fields `Space → Space` with `Space = EuclideanSpace ℝ (Fin 3)`.
- **mathlib_counterpart**: LineDeriv.laplacianCLM
- **explanation**: The definition is correct: it applies Mathlib's canonical Laplacian `Δ` to a smooth, compactly supported field ℝ³ → ℝ³ and bundles the proofs that the result is again smooth and compactly supported. The library proves that this equals the componentwise sum ∑ᵢ ∂ᵢ∂ᵢ f. However, the construction needs only a finite-dimensional real inner product space as the domain, a normed space as the codomain, and the facts that derivatives keep smoothness and compact support. The dimension 3 and the codomain ℝ³ appear only in the closure proofs, which sum over `Fin 3`. Mathlib already provides this operator in general. `TestFunction.lean` gives the test-function space 𝓓(Ω, F) the `LineDeriv`, `LineDerivAdd`, `LineDerivSMul`, `LineDerivLeftSMul` and `ContinuousLineDeriv` instances. `DerivNotation.lean` defines `LineDeriv.laplacianCLM ℝ E V₁`, the sum of second line derivatives along an orthonormal basis, as a continuous linear map V₁ → V₁. With V₁ = 𝓓(Ω, F) this is the Laplacian on test functions for any finite-dimensional real inner product space E, any open set Ω and any normed space F, together with linearity and continuity. `laplacianTest` reproduces it for the single case E = F = ℝ³ and Ω the whole space, on an ad hoc type.

### [`Chudnovsky.diagPhiQ`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Chudnovsky/SingularModuli/Rationality.lean#L65-L68) — `lean-pool-0516`

Snippet: `samples/lean-pool/lean-pool-0516.lean`

- **verdict**: `too_narrow`
- **intended_object**: The diagonal of a bivariate polynomial: for Φ(X, Y) ∈ ℚ[Y][X], the one-variable polynomial G(X) = Φ(X, X). It is used for the modular polynomial Φ_m, giving G_m(X) = Φ_m(X, X). Inferred from the docstring and from its use in Rationality.lean.
- **mathlib_counterpart**: Polynomial.eval
- **explanation**: The body is `PhiQ.eval X`. It evaluates the outer variable at the inner variable X ∈ ℚ[X], which gives exactly Φ(X, X). So the definition is mathematically correct and matches its docstring.

It takes an arbitrary element of `Polynomial (Polynomial ℚ)`, not the modular polynomial specifically, so it is the general "diagonal of a bivariate polynomial" construction. That construction makes sense over any commutative (semi)ring R: `fun p : R[X][X] => p.eval X`. Nothing in the body uses anything about ℚ.

The library itself shows the narrowness: it defines the same construction again over ℤ as `diagPhiZ`, with an identical body, and calls `diagPhiQ` "the ℚ-analogue of `diagPhiZ`". One definition parameterised by a commutative ring R would cover both. Mathlib has no named "diagonal" of a bivariate polynomial (I found nothing in `Polynomial/Bivariate.lean`), but the construction is exactly `Polynomial.eval X` at any coefficient ring. Fixing it to ℚ is a specialisation to one ring where any commutative ring works.

### [`Connes.PaperDualCoordinates.partialToDual`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConnesRigidity/Paper/Section3/DualCoordinates.lean#L177-L190) — `lean-pool-0532`

Snippet: `samples/lean-pool/lean-pool-0532.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical uncurrying map Hom_k(N, M*) → (M ⊗_k N)*, which sends g to the functional a ⊗ φ ↦ g(φ)(a). Here M = A = (Fin 3 → 𝔽₂[X]) and N = V* (the dual of the paper's 𝔽₂-space V). Inferred from the body, the name, and its use as the inverse in `dualTensorPartialEquiv`.
- **mathlib_counterpart**: TensorProduct.uncurry
- **explanation**: The body is correct. It takes g : V* →ₗ Dual k A, flips it to the bilinear map a ↦ φ ↦ g φ a, and applies `TensorProduct.lift`. The library proves that it is a two-sided inverse of `dualTensorToPartial`.

The definition is stated only for the hard-coded objects k = ZMod 2, A = Fin 3 → (ZMod 2)[X] and VStar = Dual k PaperV. None of their special features are used. The body only needs modules M and N over a commutative ring R: the map is the composite `TensorProduct.uncurry R M N R ∘ₗ LinearMap.lflip`, a linear map (N →ₗ[R] Dual R M) →ₗ[R] Dual R (M ⊗[R] N). Mathlib provides this construction in general, through `TensorProduct.uncurry` / `TensorProduct.lift.equiv` together with `LinearMap.lflip`. So the definition writes out, in one concrete setting, a generic currying construction that Mathlib already has. That makes it too narrow rather than a genuinely specific object.

### [`Grunbaum.uniformVolume`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Feige/Grunbaum/ProbabilityCore.lean#L317-L319) — `lean-pool-0540`

Snippet: `samples/lean-pool/lean-pool-0540.lean`

- **verdict**: `too_narrow`
- **intended_object**: The uniform probability distribution on a set K: Lebesgue (Haar) volume restricted to K and divided by vol(K). This comes from the docstring and from its use for centroids in the Grünbaum development.
- **mathlib_counterpart**: ProbabilityTheory.cond
- **explanation**: The body `(volume K)⁻¹ • volume.restrict K` is exactly Mathlib's conditional measure `ProbabilityTheory.cond volume K`, written `volume[|K]`. Mathlib defines it as `(μ s)⁻¹ • μ.restrict s` for any measure μ on any measurable space. As a formula it is correct. It is a probability measure when 0 < vol(K) < ∞, and the junk values for vol(K) = 0 or ∞ follow Mathlib's usual conventions.

The definition is narrower than it needs to be. Its body uses only the `MeasureSpace E` structure, through `volume`. Yet it fixes the measure to be `volume` and, through the section variables, it requires E to be a finite-dimensional real normed space with a Borel σ-algebra and an additive Haar `volume`. None of these hypotheses is used. So the definition restates, in a special setting, a construction Mathlib already provides for an arbitrary measure, namely `ProbabilityTheory.cond μ K`; Mathlib's `uniformOn` is the analogous specialization for counting measure. The definition is correct, but it duplicates the general Mathlib notion, so the verdict is too narrow.

### [`SphereOddDegree.singularChainHomotopyOfHomotopy`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/OddSphereDegree/AlgebraicTopology/Backports/PrismSimplicialHomotopy.lean#L285-L292) — `lean-pool-0561`

Snippet: `samples/lean-pool/lean-pool-0561.lean`

- **verdict**: `too_narrow`
- **intended_object**: The singular prism operator: given a homotopy H between continuous maps f, g : X → Y, the chain homotopy it induces between the singular chain maps f_#, g_# : C_•(X) → C_•(Y). The docstring and name say so.
- **mathlib_counterpart**: TopCat.Homotopy.singularChainComplexFunctorObjMap
- **explanation**: The construction itself is correct. It takes the simplicial homotopy between the singular simplicial sets that the topological homotopy induces (`prismHomotopy H`), whiskers it with the coefficient functor `sigmaConst.obj ℤ`, and turns the result into a chain homotopy. That gives a homotopy between `singularChainℤ.map f` and `singularChainℤ.map g`, as intended.

The problem is generality. The definition only covers integer coefficients in `ModuleCat ℤ` and spaces in `TopCat.{0}`. Nothing in the construction uses either restriction. Whiskering with `sigmaConst.obj R` and the passage to a chain homotopy work for any coefficient object R in any preadditive category C with coproducts, and for any universe.

Mathlib already has this general version: `TopCat.Homotopy.singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C)`, with type `Homotopy (((singularChainComplexFunctor C).obj R).map f) (((singularChainComplexFunctor C).obj R).map g)`. It is stated for any `C` with `[Preadditive C] [HasCoproducts C]` and any `X Y : TopCat.{w}`. The project's `singularChainℤ` is just `(singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)`, so this definition is the special case C = ModuleCat ℤ, R = ℤ, w = 0 of the Mathlib construction.

### [`LO.Modal.Kripke.Model.PointGenerated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Incompleteness/Foundation/Modal/Kripke/Preservation.lean#L281-L290) — `lean-pool-0562`

Snippet: `samples/lean-pool/lean-pool-0562.lean`

- **verdict**: `incorrect`
- **intended_object**: The point-generated submodel M↾r of a Kripke model M: the submodel on the worlds reachable from r (r together with everything reachable by finitely many R-steps, i.e. the R*-successors of r), with the restricted relation and valuation, rooted at r. Inferred from the name, the `↾` notation and how it is used (truth at the root is preserved, as in Blackburn–de Rijke–Venema).
- **explanation**: The definition reuses `Frame.PointGenerated`, whose worlds are `{ w | w = r ∨ r ≺ w }`. That is, r plus its *immediate* successors only, not the reflexive–transitive closure. In the literature, the point-generated subframe/submodel is closed under R, so it contains everything R*-reachable from r. The two agree only when R is transitive. Nothing in the definition assumes transitivity: it takes an arbitrary `Kripke.Model`.

Concrete discrepancy: take the chain a → b → c with p true only at c. The genuine generated submodel at a is {a, b, c}, and ◇◇p holds at a there, as it does in M. This definition gives worlds {a, b}, where ◇◇p fails at a. So the defining property of generated submodels, modal invariance at the root, fails.

The library knows this. The bisimulation and modal-equivalence lemmas (`bisimulationOfTrans`, `modal_equivalent_at_root`) all assume `IsTrans`, and every use (GL trees, S5) is on transitive frames. The `RootedFrame` notion (`isRooted`: the root sees every other world directly) is likewise tailored to transitive frames. As a definition of the point-generated submodel of an arbitrary Kripke model, it is wrong for non-transitive models. A faithful version would use the reflexive–transitive closure, or assume transitivity explicitly.

### [`Homogenization.blockMatEntry`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/Homogenization/Ambient/BlockMatrix.lean#L61-L66) — `lean-pool-0573`

Snippet: `samples/lean-pool/lean-pool-0573.lean`

- **verdict**: `too_narrow`
- **intended_object**: The entries of the 2d×2d matrix built from a 2×2 block matrix [[A₁₁, A₁₂], [A₂₁, A₂₂]] with d×d real blocks, indexed by Fin d ⊕ Fin d. Equivalently, the assembled block matrix seen as a function on the doubled index set. Inferred from the docstring and from the structure `BlockMat`.
- **mathlib_counterpart**: Matrix.fromBlocks
- **explanation**: The definition gives the right values. It splits into four cases on `Sum.inl`/`Sum.inr`, and each case returns the matching entry of the matching block: upper-left, upper-right, lower-left or lower-right. So `blockMatEntry A` equals `Matrix.fromBlocks A.upperLeft A.upperRight A.lowerLeft A.lowerRight` at every entry. There are no degenerate-case problems: for d = 0 the index type is empty and both sides are trivially equal.

The problem is generality. The body only uses case analysis on a sum type and reads entries from the four blocks. It never uses that the entries are real or that the indices are `Fin d`. Mathlib already has this construction in full generality as `Matrix.fromBlocks`, defined for blocks `Matrix n l α`, `Matrix n m α`, `Matrix o l α`, `Matrix o m α` with arbitrary index types and any entry type α. This definition rewrites it in one special setting: real entries, square blocks indexed by `Fin d`, wrapped in the library's own `BlockMat` structure.

It is also an exact copy of `toFullBlockMat`, defined a few lines earlier in the same file. Because it rewrites a general Mathlib construction in a particular setting, the verdict is too_narrow rather than faithful.

### [`composedFunction`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OSforGFF/General/FunctionalAnalysis.lean#L131-L137) — `lean-pool-0691`

Snippet: `samples/lean-pool/lean-pool-0691.lean`

- **verdict**: `too_narrow`
- **intended_object**: Composing an Lp function with a continuous linear map, f ↦ A ∘ f. This sends Lp(μ; E) to Lp(μ; F), and here it is used to lift real L² functions to complex L² functions (from the docstring and from its use with `Complex.ofRealCLM` in `embeddingRealToComplex`).
- **mathlib_counterpart**: ContinuousLinearMap.compLp
- **explanation**: The body is just `A.compLp f`. That is Mathlib's `ContinuousLinearMap.compLp`, fixed to E = ℝ, F = ℂ and p = 2. The result is correct: it does give the class of x ↦ A(f x) in L²(μ; ℂ). But nothing in it needs those choices. Mathlib's `compLp` works for any semilinear continuous map L : E →SL[σ] F between normed spaces and any exponent p : ℝ≥0∞. Mathlib also has the linear version `compLpₗ` and the continuous linear version `compLpL`. So this definition restates a general Mathlib construction in one particular setting (real-to-complex, p = 2), and the verdict is too narrow.

### [`QuantumAlg.QNNOverparametrization.IsOverparametrized`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanQuantumAlg/Primitives/QNN/Overparametrization.lean#L66-L68) — `lean-pool-0794`

Snippet: `samples/lean-pool/lean-pool-0794.lean`

- **verdict**: `incorrect`
- **intended_object**: Overparametrization of a quantum neural network in the sense of Larocca et al. (2021), arXiv:2109.11676, cited in the module docstring. A QNN with M parameters is overparametrized when the rank of its quantum Fisher information matrix reaches its maximal achievable value R_max. That value is bounded above by dim g, the dimension of the dynamical Lie algebra.
- **explanation**: The definition is simply `fisherRank M = dlaDim`. Here `dlaDim` is an opaque natural number that the docstrings say stands for dim g_S (the dimension of the dynamical Lie algebra), and `fisherRank` is an abstract monotone function bounded by it. So the definition says the QFIM rank equals the dimension of the dynamical Lie algebra. That matches the docstring, but not the notion it formalizes.

In Larocca et al., overparametrization means the QFIM rank reaches the maximal achievable rank R_max. The dynamical Lie algebra dimension is only an upper bound, R_max ≤ dim g. In general this bound is strict, because for a pure input state the rank is at most the dimension of the state's orbit, which is dim g minus the dimension of the state's stabilizer subalgebra.

Concrete case: one qubit with a universal circuit. Here g = su(2), so dim g = 3, but the orbit of a pure state is the Bloch sphere, so the QFIM rank never exceeds 2. In the paper's sense this QNN is overparametrized once its rank reaches 2, which takes two or three parameters. Under this definition, with `dlaDim = 3`, it is never overparametrized for any M.

So the definition swaps "saturates the maximal achievable rank" for "saturates the DLA bound". These agree only when the bound happens to be tight. Setting `dlaDim := R_max` would give the right notion, but that contradicts the stated meaning of `dlaDim`. The whole construction is also a thin abstract wrapper, since `dlaDim` is not connected to any actual Lie algebra.

### [`Matrix.IsHermitian.rpow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/Matrix/PosDefRpow.lean#L36-L41) — `lean-pool-0808`

Snippet: `samples/lean-pool/lean-pool-0808.lean`

- **verdict**: `too_narrow`
- **intended_object**: The real power Q^r of a Hermitian (in practice positive (semi)definite) matrix, defined by functional calculus: Q^r = U·diag(λ_i^r)·U*, where Q = U·diag(λ)·U* is the spectral decomposition. Inferred from the docstring ("Real powers of a Hermitian matrix, defined by spectral calculus") and the file name PosDefRpow.
- **mathlib_counterpart**: CFC.rpow
- **explanation**: The definition is correct for what it describes. `innerAut U x` is `U * x * star U` (by `innerAut_apply'`), so the body is U·diag(ofReal(λ_i ^ r))·U* with U = `hQ.eigenvectorUnitary`. This is exactly Mathlib's `Matrix.IsHermitian.cfc (fun x => x ^ r)`, which `Matrix.IsHermitian.cfc_eq` shows equals the generic `cfc (fun x : ℝ => x ^ r) Q`.

For positive semidefinite Q it also agrees with Mathlib's `CFC.rpow Q r := cfc (fun x : ℝ≥0 => x ^ r) Q`, including at a zero eigenvalue: 0^0 = 1 and 0^r = 0 for r ≠ 0, under both `Real.rpow` and `NNReal.rpow`. On negative eigenvalues the value comes from `Real.rpow`'s convention for negative bases, which lies outside the natural domain, so it is not an error.

So it does define the intended object. But it writes out, for matrices only, a construction Mathlib provides in general. Real powers of nonnegative elements are defined in Mathlib by continuous functional calculus for any star-ordered algebra with an `IsSelfAdjoint` ℝ-functional calculus and nonnegative spectra: `CFC.rpow`, with notation `a ^ r`. More generally, `cfc (· ^ r)` gives the same thing for self-adjoint elements. Mathlib supplies these instances for `Matrix n n 𝕜` (`Matrix.IsHermitian.instContinuousFunctionalCalculus`, with the `MatrixOrder` scope this file already opens). The construction uses nothing specific to matrices beyond the spectral theorem, which the functional calculus abstracts. Mathlib's own matrix version, `Matrix.IsHermitian.cfc`, has a docstring telling users to prefer the generic API.

The natural generality is therefore C*-algebras with continuous functional calculus, as in `CFC.rpow`, and this matrix-only, eigenvector-based definition is narrower than that.

### [`MarkovProcess.PositiveC0ContractiveResolvent.onePointRemainder`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkovProcess/MarkovProcess/Kernel/OnePointExtension.lean#L128-L136) — `lean-pool-0850`

Snippet: `samples/lean-pool/lean-pool-0850.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical map from continuous functions on the one-point compactification X∪{∞} to C₀(X): g ↦ g|_X − g(∞). It is the C₀(X) part of the decomposition C(X∪{∞}) ≅ C₀(X) ⊕ ℝ. This comes from the docstring and from how the file uses it, together with `onePointAssemble`.
- **mathlib_counterpart**: ContinuousMap.toZeroAtInfty
- **explanation**: The definition is mathematically correct. It sends g to the function x ↦ g(↑x) − g(∞), which is continuous and tends to 0 at infinity. The input type is C₀(OnePoint X, ℝ) rather than C(OnePoint X, ℝ), but the two are the same because OnePoint X is compact.

However, Mathlib already has this construction in `Mathlib/Topology/ContinuousMap/ZeroAtInftyUnitization.lean`: `ContinuousMap.toZeroAtInfty : C(OnePoint X, R) → C₀(X, R)`, `g ↦ fun x ↦ g x − g ∞`. It also provides the linear-map version `toZeroAtInftyLinearMap` and the inverse equivalence `unitizationEquiv`. Mathlib's version only assumes `[R1Space X]`, and R can be any topological additive commutative group.

The library's version fixes the codomain to ℝ. Through the section variables it also requires X to be T2, locally compact and second countable. The proof only uses the subtraction in ℝ and the fact that coclosedCompact equals cocompact, and the latter already holds in R1 spaces. So none of these special hypotheses is needed, and the library re-implements in one special setting a construction Mathlib provides in general.

### [`Module.Basis.toQuotient`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BruhatTits/Lattice/Quotient.lean#L94-L118) — `lean-pool-0871`

Snippet: `samples/lean-pool/lean-pool-0871.lean`

- **verdict**: `too_narrow`
- **intended_object**: Given an R-basis b of a lattice L, the induced R/𝔪-basis i ↦ [b i] of L/𝔪L (equivalently L/ϖL); source: the docstring and module doc. In general: a basis of a free R-module M induces a basis of M/IM over R/I.
- **mathlib_counterpart**: IsLocalRing.basisQuotient
- **explanation**: The construction is correct: the vectors are the images of b i under the quotient map L → L/𝔪L, and they form an R/𝔪-basis. Spanning is shown by span induction, pushing scalars through R → R/𝔪. Linear independence follows from a dimension count (finrank = 2 = card (Fin 2)). That count comes from the library's own `quotient_finrank_eq`, which already holds for any commutative ring R, ideal I and basis indexed by any finite ι. None of the special hypotheses are used: DVR, fraction field, lattices in K², index Fin 2, maximal ideal. The standard statement, that a basis (b_i) of a free R-module M induces the basis ([b_i]) of M/IM over R/I, holds for any commutative ring, any ideal and any index type. Mathlib already has it for finite free algebras over a local ring (`IsLocalRing.basisQuotient`, giving S/𝔪S over R/𝔪), and the module version can be built from `Basis.baseChange` and `quotTensorEquivQuotSMul`. Hard-coding Fin 2 and rank-2 lattices over a DVR is therefore narrower than the construction's natural setting.

### [`SphereOddDegree.sect`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/OddSphereDegree/AlgebraicTopology/PrismOperator.lean#L80-L83) — `lean-pool-0978`

Snippet: `samples/lean-pool/lean-pool-0978.lean`

- **verdict**: `too_narrow`
- **intended_object**: The j-th endpoint inclusion of the simplicial cylinder, i_j : K → K × Δ[1], x ↦ (x, j), here only for K = Sing X. Inferred from the docstring and from its use alongside the `cylinder` construction.
- **mathlib_counterpart**: SSet.ι₀
- **explanation**: The body is `prod.lift (𝟙 _) (vtx _ j)`: the identity in the first component and the constant map to vertex j of Δ[1] in the second. This is the endpoint inclusion i_j, so the definition is correct. However, it uses nothing specific to Sing X: `vtx` is defined for an arbitrary `Z : SSet`, and only binary products are needed. The same map exists for every simplicial set K. Mathlib already provides it in that generality as `SSet.ι₀` and `SSet.ι₁ : X ⟶ X ⊗ Δ[1]` (Mathlib/AlgebraicTopology/SimplicialSet/Monoidal.lean). The lemmas `ι₀_fst` and `ι₀_snd` there show that `SSet.ι₀` has exactly the same two components (the identity and `const (stdSimplex.obj₀Equiv.symm 0)`). Mathlib's version uses the monoidal product `⊗` rather than `⨯`, which for simplicial sets is canonically the same. Mathlib also applies `SSet.ι₀` to Sing X directly in TopAdj.lean. So this definition restricts to Sing X a construction that Mathlib provides for all simplicial sets.

### [`AVenhance.Infra.Section5.materialDerivative`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/MaterialGradient.lean#L25-L28) — `lean-pool-0990`

Snippet: `samples/lean-pool/lean-pool-0990.lean`

- **verdict**: `too_narrow`
- **intended_object**: The material (advective/convective) derivative of a scalar field T along a velocity field b: D_t T = ∂_t T + b·∇T, evaluated at (t, x). This comes from the docstring, the module and the lemma materialDerivative_eq_advective_of_hasFDerivAt.
- **explanation**: The body is fderiv ℝ (uncurry T) (t, x) (1, b t x), the space–time Fréchet derivative applied in the direction (1, b(t, x)). When T is differentiable, linearity splits this into ∂_t T + D_x T · b = ∂_t T + b·∇T, which is the material derivative. The library proves this in materialDerivative_eq_advective_of_hasFDerivAt. Where T is not differentiable the value is 0, which is the standard fderiv junk value. So the definition is mathematically correct.

However, it is fixed to Vec 2 = Fin 2 → ℝ, and the body uses no property of this space. The same expression type-checks with any real normed space E in place of Vec 2: T : ℝ → E → F and b : ℝ → E → E, with F any normed space. In particular it works for any dimension d, using the library's own Vec d. The material derivative is defined in arbitrary dimension (and for vector-valued fields) in the literature. Only the companion lemmas that express it through coordinates (vecDot, basisVec, Fin.sum_univ_two) use the 2D structure; the definition itself does not. Fixing the dimension at 2 is therefore an unnecessary specialization. Mathlib has no material-derivative declaration, so there is no counterpart to cite.

### [`IsTransvec`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/HeckeRIngs/GLn/SLnTransvection.lean#L29-L32) — `lean-pool-0993`

Snippet: `samples/lean-pool/lean-pool-0993.lean`

- **verdict**: `too_narrow`
- **intended_object**: The property of an element of SL_m(ℤ) being an elementary transvection, i.e. a matrix I + c·E_{ij} with i ≠ j. This comes from the docstring, from `slTransvecG`, and from the module doc (SL_n(ℤ) is generated by transvections).
- **mathlib_counterpart**: Matrix.TransvectionStruct
- **explanation**: As a characterization, the definition is correct: E is a transvection exactly when it equals `⟨Matrix.transvection i j c, _⟩` for some i ≠ j and some c. That matches the elementary matrices I + c·E_{ij} from the literature.

The setting is narrower than it needs to be, though. Nothing in the construction uses anything special about ℤ or `Fin m`. `Matrix.transvection i j c` and `Matrix.det_transvection_of_ne` work over any commutative ring R and any finite index type n with decidable equality. So the predicate "E ∈ SL_n(R) is an elementary transvection" makes sense in that generality.

Mathlib already has this general notion. `Matrix.TransvectionStruct n R` packages the data (i, j, i ≠ j, c) over any index type and any ring, and `TransvectionStruct.toMatrix` turns it into the matrix. `Matrix.GeneralLinearGroup.transvection` gives the same matrix as an element of GL_n(R) for general R. A general version of `IsTransvec` would just say that E lies in the range of `TransvectionStruct.toMatrix` (lifted to SL_n(R)).

The file's main theorem, that SL_n(ℤ) is generated by transvections, does need ℤ, since its proof relies on division with remainder. The definition of the predicate does not need ℤ. Fixing both the ring as ℤ and the index type as `Fin m` therefore makes the definition too narrow.


## FLT (Anthropic) (1000 flagged)

### [`P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two.STAB2E100.negVC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two.lean#L65-L65) — `flt-anthropic-0000`

Snippet: `samples/flt-anthropic/flt-anthropic-0000.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor.entryAdele`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean#L241-L245) — `flt-anthropic-0001`

Snippet: `samples/flt-anthropic/flt-anthropic-0001.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.SubalgebraStages.specCone`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_SubalgebraStages.lean#L50-L55) — `flt-anthropic-0002`

Snippet: `samples/flt-anthropic/flt-anthropic-0002.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.OrbitStabFin.underS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.lean#L34-L34) — `flt-anthropic-0003`

Snippet: `samples/flt-anthropic/flt-anthropic-0003.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.P2mInertEvalGlue.unitNorm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.lean#L240-L241) — `flt-anthropic-0004`

Snippet: `samples/flt-anthropic/flt-anthropic-0004.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules.FrameBridge.secX`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean#L65-L65) — `flt-anthropic-0005`

Snippet: `samples/flt-anthropic/flt-anthropic-0005.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two.W1xLA.τEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two.lean#L976-L977) — `flt-anthropic-0006`

Snippet: `samples/flt-anthropic/flt-anthropic-0006.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPlaneModel.J1ThirteenPicZeroFibreDiamond.J1ThirteenPicZeroLiteralChordChain.J1ThirteenPicZeroPlaceDictionary.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction.J1ThirteenPicZeroLitPic0Comparison.J1ThirteenX113RiemannRochRows.MazurTate1973Mt31b.J1ThirteenX113PackageHeldRowOne.MilneAvAg9bRd9DictionaryHeld3Closure.J1ThirteenX113OrdRowWellDefinedReduction.MilneAvAg9bRd10EllKFinUpperRow.MilneAvAg9bRd11X113TowerPowerBasis.Ag9b11bX113HwdUnitDischarge.MilneAvAg9bRd11DictionaryBinderShrink.MilneAvAg9bRd12X113AssemblyRetirement.MilneAvAg9bRd12T1P1InftyResidue.MilneAvAg9bRd12X113LocalDatumMint.MilneAvAg9bRd12X113FiveRowUpgrade.AlgebraicCurve.HasSeparatingTranscendentalCore`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L9415-L9416) — `flt-anthropic-0007`

Snippet: `samples/flt-anthropic/flt-anthropic-0007.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.AuxLevel.midML`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CuspForm_AuxLevelHeckeModuleMid.lean#L31-L34) — `flt-anthropic-0008`

Snippet: `samples/flt-anthropic/flt-anthropic-0008.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard.K3Far.liftSnd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.lean#L93-L102) — `flt-anthropic-0009`

Snippet: `samples/flt-anthropic/flt-anthropic-0009.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.RATIOCOVER.weyl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.lean#L29-L37) — `flt-anthropic-0010`

Snippet: `samples/flt-anthropic/flt-anthropic-0010.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.Modules.IsSectionBasisOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FramedPolarisedAbelianScheme.lean#L17-L20) — `flt-anthropic-0011`

Snippet: `samples/flt-anthropic/flt-anthropic-0011.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation.pre`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.lean#L455-L462) — `flt-anthropic-0012`

Snippet: `samples/flt-anthropic/flt-anthropic-0012.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3.IsKfSm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.lean#L61-L63) — `flt-anthropic-0013`

Snippet: `samples/flt-anthropic/flt-anthropic-0013.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP.fromOrient`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.lean#L354-L359) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.PDPairing.sect`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_PDPairing.lean#L461-L462) — `flt-anthropic-0015`

Snippet: `samples/flt-anthropic/flt-anthropic-0015.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two.MuTwoGroupAlgebraRepr.GroupAlgebraPoints.C2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two.lean#L163-L163) — `flt-anthropic-0016`

Snippet: `samples/flt-anthropic/flt-anthropic-0016.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel.zeta0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean#L868-L869) — `flt-anthropic-0017`

Snippet: `samples/flt-anthropic/flt-anthropic-0017.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.BridgeCup.zetaq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.lean#L408-L411) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.lean#L2189-L2194) — `flt-anthropic-0019`

Snippet: `samples/flt-anthropic/flt-anthropic-0019.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD.divP`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.lean#L158-L158) — `flt-anthropic-0020`

Snippet: `samples/flt-anthropic/flt-anthropic-0020.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.FormalOmega.AlgFunctor.GroupAction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean#L60-L67) — `flt-anthropic-0021`

Snippet: `samples/flt-anthropic/flt-anthropic-0021.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.P2mOctCompare.Hex`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.lean#L13-L13) — `flt-anthropic-0022`

Snippet: `samples/flt-anthropic/flt-anthropic-0022.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NeronModelInfra.schemeHomOverEquivOverHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean#L46-L51) — `flt-anthropic-0023`

Snippet: `samples/flt-anthropic/flt-anthropic-0023.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4.W1xLA.Good`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4.lean#L841-L842) — `flt-anthropic-0024`

Snippet: `samples/flt-anthropic/flt-anthropic-0024.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3.S`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.lean#L230-L232) — `flt-anthropic-0025`

Snippet: `samples/flt-anthropic/flt-anthropic-0025.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.ModularCurve.PDPairing.TD.HFun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean#L2707-L2709) — `flt-anthropic-0026`

Snippet: `samples/flt-anthropic/flt-anthropic-0026.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot.TateTransfer.Arith.sB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot.lean#L87-L87) — `flt-anthropic-0027`

Snippet: `samples/flt-anthropic/flt-anthropic-0027.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH.ModularCurve.LinAuxW.expZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH.lean#L232-L232) — `flt-anthropic-0028`

Snippet: `samples/flt-anthropic/flt-anthropic-0028.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.Ws25.KummerO.PointsDict.pointsEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.lean#L1721-L1725) — `flt-anthropic-0029`

Snippet: `samples/flt-anthropic/flt-anthropic-0029.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.XI`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean#L17-L17) — `flt-anthropic-0030`

Snippet: `samples/flt-anthropic/flt-anthropic-0030.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex.AVC15.pairPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex.lean#L57-L58) — `flt-anthropic-0031`

Snippet: `samples/flt-anthropic/flt-anthropic-0031.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.FinFlatHopf.W4.moduleScal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.lean#L1441-L1443) — `flt-anthropic-0032`

Snippet: `samples/flt-anthropic/flt-anthropic-0032.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.TPIN.Ent`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.lean#L234-L236) — `flt-anthropic-0033`

Snippet: `samples/flt-anthropic/flt-anthropic-0033.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld.KernelIdealDescent.homGrp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.lean#L258-L262) — `flt-anthropic-0034`

Snippet: `samples/flt-anthropic/flt-anthropic-0034.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine.Setup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.lean#L15-L42) — `flt-anthropic-0035`

Snippet: `samples/flt-anthropic/flt-anthropic-0035.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime.CerednikDrinfeld.QM.FakeEllipticCurve.Pts.val`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime.lean#L59-L59) — `flt-anthropic-0036`

Snippet: `samples/flt-anthropic/flt-anthropic-0036.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isEichlerOrder_forall_mem_awayUnits_iff_forall_exists_smul_mem_preservesLevel_and_exists_isMaximalOrder_inf_eq_of_isPullback_prod.LStabAsm.e10`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isEichlerOrder_forall_mem_awayUnits_iff_forall_exists_smul_mem_preservesLevel_and_exists_isMaximalOrder_inf_eq_of_isPullback_prod.lean#L475-L478) — `flt-anthropic-0037`

Snippet: `samples/flt-anthropic/flt-anthropic-0037.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier.RowModule.rowModulus`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.lean#L247-L250) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux.basePt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.lean#L163-L164) — `flt-anthropic-0039`

Snippet: `samples/flt-anthropic/flt-anthropic-0039.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity.M4aHerbrand.Rigidity.singleFinStratum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_adeleBaseChange_local_rigidity.lean#L414-L421) — `flt-anthropic-0040`

Snippet: `samples/flt-anthropic/flt-anthropic-0040.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam.LambdaGhost.inv1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam.lean#L30-L30) — `flt-anthropic-0041`

Snippet: `samples/flt-anthropic/flt-anthropic-0041.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_seed_package_of_mem_span_archDeriv_translate.R1CuspDeriv.ofRealHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_seed_package_of_mem_span_archDeriv_translate.lean#L80-L81) — `flt-anthropic-0042`

Snippet: `samples/flt-anthropic/flt-anthropic-0042.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.Omega.edgeTube`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_OmegaTubes.lean#L29-L30) — `flt-anthropic-0043`

Snippet: `samples/flt-anthropic/flt-anthropic-0043.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.R1Kit.twistStepTopIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.lean#L133-L137) — `flt-anthropic-0044`

Snippet: `samples/flt-anthropic/flt-anthropic-0044.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.R4EmbedM2.retr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.lean#L20-L21) — `flt-anthropic-0045`

Snippet: `samples/flt-anthropic/flt-anthropic-0045.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`MvPolynomial.CrossingQuotient.quotIUEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_MvPolynomial_CrossingResolutionFibrePoints.lean#L676-L678) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint.W1xLA.qC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint.lean#L361-L361) — `flt-anthropic-0047`

Snippet: `samples/flt-anthropic/flt-anthropic-0047.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.MultCovering.nodeSrc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_MultCoveringCharts.lean#L123-L124) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.ESD3.idxEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.lean#L425-L426) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`MvFormalGroup.ofMv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_MvFormalGroup_OfFormalGroupV2.lean#L198-L198) — `flt-anthropic-0050`

Snippet: `samples/flt-anthropic/flt-anthropic-0050.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.B26.rO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.lean#L19-L20) — `flt-anthropic-0051`

Snippet: `samples/flt-anthropic/flt-anthropic-0051.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.S17Torsor.β`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.lean#L131-L132) — `flt-anthropic-0052`

Snippet: `samples/flt-anthropic/flt-anthropic-0052.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom.principalIdeles`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.lean#L25-L26) — `flt-anthropic-0053`

Snippet: `samples/flt-anthropic/flt-anthropic-0053.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.S42LevelHopf.Calg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.lean#L109-L109) — `flt-anthropic-0054`

Snippet: `samples/flt-anthropic/flt-anthropic-0054.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.Theta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1241-L1245) — `flt-anthropic-0055`

Snippet: `samples/flt-anthropic/flt-anthropic-0055.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.P2mKcQmBcSol.SqHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.lean#L75-L77) — `flt-anthropic-0056`

Snippet: `samples/flt-anthropic/flt-anthropic-0056.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand.R4GC.upSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand.lean#L102-L102) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.Sum56K6.i6`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.lean#L481-L481) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.Differential.pullbackAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean#L16-L19) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`WeierstrassCurve.variableChangeDenom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_VariableChangeSeries.lean#L14-L15) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PadicInt_exists_etale_algebra_algHom_equiv_zmod.UnramLayer.kOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PadicInt_exists_etale_algebra_algHom_equiv_zmod.lean#L254-L255) — `flt-anthropic-0061`

Snippet: `samples/flt-anthropic/flt-anthropic-0061.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.WeierstrassCurve.Affine.mapPoint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean#L6641-L6642) — `flt-anthropic-0062`

Snippet: `samples/flt-anthropic/flt-anthropic-0062.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio.FLT.AdmissibleRep.fixedVectors`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio.lean#L1391-L1400) — `flt-anthropic-0063`

Snippet: `samples/flt-anthropic/flt-anthropic-0063.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one.M4aLocalCFT.FujisakiC2a.unitElem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one.lean#L3699-L3699) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.IsModuliPlaceOfFrobSmulSol.twPlace`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.lean#L37-L43) — `flt-anthropic-0065`

Snippet: `samples/flt-anthropic/flt-anthropic-0065.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.IsIntegralAdjoinCoeffEmbJqInvSol.Lc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.lean#L116-L117) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal.tMi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.lean#L430-L430) — `flt-anthropic-0067`

Snippet: `samples/flt-anthropic/flt-anthropic-0067.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.comapSubschemeMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_UniversalDivisor.lean#L74-L76) — `flt-anthropic-0068`

Snippet: `samples/flt-anthropic/flt-anthropic-0068.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.KbManinAnyChar.sig3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.lean#L552-L552) — `flt-anthropic-0069`

Snippet: `samples/flt-anthropic/flt-anthropic-0069.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.Ws50Read.shuffle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean#L77-L79) — `flt-anthropic-0070`

Snippet: `samples/flt-anthropic/flt-anthropic-0070.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.E4AV_CuPoleFst.algebraFbShortcut`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.lean#L61-L62) — `flt-anthropic-0071`

Snippet: `samples/flt-anthropic/flt-anthropic-0071.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.WhitIBP.ℓ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean#L310-L310) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.EsUPar.PerU.beta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.lean#L165-L166) — `flt-anthropic-0073`

Snippet: `samples/flt-anthropic/flt-anthropic-0073.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.G4Sol.OA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.lean#L426-L426) — `flt-anthropic-0074`

Snippet: `samples/flt-anthropic/flt-anthropic-0074.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots.GaussPencil.ratFuncMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots.lean#L394-L399) — `flt-anthropic-0075`

Snippet: `samples/flt-anthropic/flt-anthropic-0075.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`TwoChartCech.Mumford.quot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean#L56-L57) — `flt-anthropic-0076`

Snippet: `samples/flt-anthropic/flt-anthropic-0076.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux.ASys.T3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.lean#L269-L269) — `flt-anthropic-0077`

Snippet: `samples/flt-anthropic/flt-anthropic-0077.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`GaloisRep.InertiaRing.mkO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GaloisRep_InertiaRing.lean#L32-L35) — `flt-anthropic-0078`

Snippet: `samples/flt-anthropic/flt-anthropic-0078.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.pointPullbackHomTo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean#L456-L460) — `flt-anthropic-0079`

Snippet: `samples/flt-anthropic/flt-anthropic-0079.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness.QB.sPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness.lean#L190-L190) — `flt-anthropic-0080`

Snippet: `samples/flt-anthropic/flt-anthropic-0080.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.TwistMain.coordW`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean#L595-L595) — `flt-anthropic-0081`

Snippet: `samples/flt-anthropic/flt-anthropic-0081.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.AlgebraicCurve.CentredPlaceRigidity.evalMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean#L173-L174) — `flt-anthropic-0082`

Snippet: `samples/flt-anthropic/flt-anthropic-0082.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.PInf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L272-L273) — `flt-anthropic-0083`

Snippet: `samples/flt-anthropic/flt-anthropic-0083.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel.L1Asm22.Main.Zsub`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel.lean#L1790-L1790) — `flt-anthropic-0084`

Snippet: `samples/flt-anthropic/flt-anthropic-0084.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.EDB.Coord.N1'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.lean#L224-L225) — `flt-anthropic-0085`

Snippet: `samples/flt-anthropic/flt-anthropic-0085.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.kdAb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.lean#L474-L482) — `flt-anthropic-0086`

Snippet: `samples/flt-anthropic/flt-anthropic-0086.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.LC2.mass`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean#L379-L379) — `flt-anthropic-0087`

Snippet: `samples/flt-anthropic/flt-anthropic-0087.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.ModularCurve.PDPairing.TD.faceGen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean#L4974-L4974) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel.K1Road.qExpandBar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.lean#L41-L49) — `flt-anthropic-0089`

Snippet: `samples/flt-anthropic/flt-anthropic-0089.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.GoodReductionJacobian.RelativeGroupLaw.SpreadEtale.fstPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.lean#L38-L39) — `flt-anthropic-0090`

Snippet: `samples/flt-anthropic/flt-anthropic-0090.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.NilYoneda.transition`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.lean#L227-L228) — `flt-anthropic-0091`

Snippet: `samples/flt-anthropic/flt-anthropic-0091.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq.FltWs24.Asm.D2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq.lean#L851-L859) — `flt-anthropic-0092`

Snippet: `samples/flt-anthropic/flt-anthropic-0092.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData.prπ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean#L140-L140) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_isFreeGroup_Gamma_four.ModularCurve.PDPairing.BaseTwo.cuspGen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_isFreeGroup_Gamma_four.lean#L2065-L2067) — `flt-anthropic-0094`

Snippet: `samples/flt-anthropic/flt-anthropic-0094.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt.Θ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.lean#L38-L40) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2.EV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.lean#L117-L118) — `flt-anthropic-0096`

Snippet: `samples/flt-anthropic/flt-anthropic-0096.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TateCurve_symAdd_sum_regional.TateCurve.TateCurve.TateCurve.s1PosSupport`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_symAdd_sum_regional.lean#L2876-L2876) — `flt-anthropic-0097`

Snippet: `samples/flt-anthropic/flt-anthropic-0097.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.NormKit.S`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.lean#L744-L748) — `flt-anthropic-0098`

Snippet: `samples/flt-anthropic/flt-anthropic-0098.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.TOLD0b.Γ1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean#L24-L25) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.CellPeriods.wordMatrix`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.lean#L1270-L1272) — `flt-anthropic-0100`

Snippet: `samples/flt-anthropic/flt-anthropic-0100.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum.germ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.lean#L510-L511) — `flt-anthropic-0101`

Snippet: `samples/flt-anthropic/flt-anthropic-0101.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv.ofRealHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.lean#L2858-L2859) — `flt-anthropic-0102`

Snippet: `samples/flt-anthropic/flt-anthropic-0102.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp.UqNSol.resHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp.lean#L735-L741) — `flt-anthropic-0103`

Snippet: `samples/flt-anthropic/flt-anthropic-0103.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele.CerednikDrinfeld.BrandtLevel.place`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele.lean#L1834-L1835) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.HopfAlgebra.HopfIdealQuotient.antipodeAlgHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean#L48-L51) — `flt-anthropic-0105`

Snippet: `samples/flt-anthropic/flt-anthropic-0105.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm.Cos`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.lean#L27-L27) — `flt-anthropic-0106`

Snippet: `samples/flt-anthropic/flt-anthropic-0106.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve.QExpSplitDevissage.vcTheta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.lean#L314-L314) — `flt-anthropic-0107`

Snippet: `samples/flt-anthropic/flt-anthropic-0107.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve.QExpSplitDevissage.vcForm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.lean#L96-L99) — `flt-anthropic-0108`

Snippet: `samples/flt-anthropic/flt-anthropic-0108.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint.ModularCurve.ModularCurve.modularEvalF`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint.lean#L341-L343) — `flt-anthropic-0109`

Snippet: `samples/flt-anthropic/flt-anthropic-0109.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.Γℚ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.lean#L14-L14) — `flt-anthropic-0110`

Snippet: `samples/flt-anthropic/flt-anthropic-0110.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic.altInsert`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.lean#L100-L103) — `flt-anthropic-0111`

Snippet: `samples/flt-anthropic/flt-anthropic-0111.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom.AlgebraicGeometry.Scheme.Modules.Hom.restrictScalarsSelfEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom.lean#L111-L113) — `flt-anthropic-0112`

Snippet: `samples/flt-anthropic/flt-anthropic-0112.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0.INVOL.WData`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0.lean#L243-L248) — `flt-anthropic-0113`

Snippet: `samples/flt-anthropic/flt-anthropic-0113.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_eichlerShimuraMap_heckeTLin.HeckeEis.HeckeESSol.HeckeAnalytic.repMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_eichlerShimuraMap_heckeTLin.lean#L34-L36) — `flt-anthropic-0114`

Snippet: `samples/flt-anthropic/flt-anthropic-0114.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.IntTwoCuspForms`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_XHDifferentialsModL.lean#L374-L375) — `flt-anthropic-0115`

Snippet: `samples/flt-anthropic/flt-anthropic-0115.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_petersson_heckeTLin.AlliAux1R6.Bez.Ymat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_petersson_heckeTLin.lean#L930-L934) — `flt-anthropic-0116`

Snippet: `samples/flt-anthropic/flt-anthropic-0116.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.FinFlatHopf.W4.reprOneTmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.lean#L814-L821) — `flt-anthropic-0117`

Snippet: `samples/flt-anthropic/flt-anthropic-0117.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.P2mLaw535G.U2'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.lean#L644-L644) — `flt-anthropic-0118`

Snippet: `samples/flt-anthropic/flt-anthropic-0118.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_RubinSilverberg_not_dvd_den_coeff.RubinSilverberg.polyB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_not_dvd_den_coeff.lean#L243-L244) — `flt-anthropic-0119`

Snippet: `samples/flt-anthropic/flt-anthropic-0119.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank.MoritaLine.ofPi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank.lean#L73-L78) — `flt-anthropic-0120`

Snippet: `samples/flt-anthropic/flt-anthropic-0120.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`PresheafOfModules.PullbackMonoidal.pf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_PresheafOfModules_PullbackMonoidal.lean#L222-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top.JacquetEmbeddingGL2.VN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top.lean#L314-L316) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_auxLevel_of_charpoly_frobenius_eq.TWAlphaTransport.mapL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_auxLevel_of_charpoly_frobenius_eq.lean#L118-L138) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul.SMOVpG1.ratMatrix`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul.lean#L163-L165) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two.P2MKcCENH2.Param`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_two.lean#L413-L414) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModPForms_finiteDimensional_modPMod.RedRank.latt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModPForms_finiteDimensional_modPMod.lean#L91-L99) — `flt-anthropic-0126`

Snippet: `samples/flt-anthropic/flt-anthropic-0126.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial.LinearMap.FlatKerBC.theta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial.lean#L94-L96) — `flt-anthropic-0127`

Snippet: `samples/flt-anthropic/flt-anthropic-0127.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable.CvqOrbit.toAnnulusDatum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable.lean#L565-L576) — `flt-anthropic-0128`

Snippet: `samples/flt-anthropic/flt-anthropic-0128.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor.Gsl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean#L33-L35) — `flt-anthropic-0129`

Snippet: `samples/flt-anthropic/flt-anthropic-0129.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed.P2mKcUnitRootLattice.LPi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed.lean#L283-L283) — `flt-anthropic-0130`

Snippet: `samples/flt-anthropic/flt-anthropic-0130.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE.resE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.lean#L1898-L1899) — `flt-anthropic-0131`

Snippet: `samples/flt-anthropic/flt-anthropic-0131.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top.E5Bridge.θb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top.lean#L376-L379) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.LanglandsTunnell.P0.redc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.lean#L162-L162) — `flt-anthropic-0133`

Snippet: `samples/flt-anthropic/flt-anthropic-0133.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.FormalODModule.gradedPiece`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_CartierGradedPiece.lean#L21-L28) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine.EtaleEdgeChart.coord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine.lean#L112-L126) — `flt-anthropic-0135`

Snippet: `samples/flt-anthropic/flt-anthropic-0135.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold.wt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.lean#L204-L205) — `flt-anthropic-0136`

Snippet: `samples/flt-anthropic/flt-anthropic-0136.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.Modules.fibration`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ThetaGroup.lean#L98-L99) — `flt-anthropic-0137`

Snippet: `samples/flt-anthropic/flt-anthropic-0137.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.Reduce95.alFs`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.lean#L3141-L3142) — `flt-anthropic-0138`

Snippet: `samples/flt-anthropic/flt-anthropic-0138.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.SemilinearAut.IsNodeStable`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_GluedPic0Functoriality.lean#L40-L41) — `flt-anthropic-0139`

Snippet: `samples/flt-anthropic/flt-anthropic-0139.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_nonempty_patchingDatum_of_levelData.M4cP4Glue.Lam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_nonempty_patchingDatum_of_levelData.lean#L34-L34) — `flt-anthropic-0140`

Snippet: `samples/flt-anthropic/flt-anthropic-0140.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.vsMapEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.lean#L787-L788) — `flt-anthropic-0141`

Snippet: `samples/flt-anthropic/flt-anthropic-0141.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.WeierstrassCurve.Affine.geomDivisorSum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L1021-L1022) — `flt-anthropic-0142`

Snippet: `samples/flt-anthropic/flt-anthropic-0142.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero.P2mKuroshSpan.G23`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero.lean#L438-L438) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries.sumToFun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean#L62-L63) — `flt-anthropic-0144`

Snippet: `samples/flt-anthropic/flt-anthropic-0144.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1_mul.INVOL.WData`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1_mul.lean#L239-L244) — `flt-anthropic-0145`

Snippet: `samples/flt-anthropic/flt-anthropic-0145.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash.WcPort.toALData`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_alSlash_add_heckeU_alSlash_alSlash.lean#L2361-L2362) — `flt-anthropic-0146`

Snippet: `samples/flt-anthropic/flt-anthropic-0146.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.LevelP.smulX`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_KatzLevelPQuotient.lean#L16-L17) — `flt-anthropic-0147`

Snippet: `samples/flt-anthropic/flt-anthropic-0147.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.AutomorphicForm.WeylIntegrable.mInvMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean#L885-L886) — `flt-anthropic-0148`

Snippet: `samples/flt-anthropic/flt-anthropic-0148.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.AXL.E`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.lean#L306-L306) — `flt-anthropic-0149`

Snippet: `samples/flt-anthropic/flt-anthropic-0149.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso.ιd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.lean#L132-L132) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three.K3a3Chi.adj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three.lean#L29-L30) — `flt-anthropic-0151`

Snippet: `samples/flt-anthropic/flt-anthropic-0151.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.F6ea14e94.mulSec`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.lean#L47-L49) — `flt-anthropic-0152`

Snippet: `samples/flt-anthropic/flt-anthropic-0152.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.OModulePresheaf.HSucc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean#L139-L140) — `flt-anthropic-0153`

Snippet: `samples/flt-anthropic/flt-anthropic-0153.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.P2.Artin.IsAdmissibleModulus`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_ArtinCoreCTM.lean#L311-L312) — `flt-anthropic-0154`

Snippet: `samples/flt-anthropic/flt-anthropic-0154.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.P2mGExt.Chunk.divl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean#L430-L430) — `flt-anthropic-0155`

Snippet: `samples/flt-anthropic/flt-anthropic-0155.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer.OVbProof.NSub`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_common_overlayer.lean#L162-L162) — `flt-anthropic-0156`

Snippet: `samples/flt-anthropic/flt-anthropic-0156.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.P2mKcQuadrupleCor.awayMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.lean#L27-L29) — `flt-anthropic-0157`

Snippet: `samples/flt-anthropic/flt-anthropic-0157.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two.AutomorphicForm.LocalCentralPair.sc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two.lean#L33-L33) — `flt-anthropic-0158`

Snippet: `samples/flt-anthropic/flt-anthropic-0158.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules.RatSec.eApp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.lean#L87-L88) — `flt-anthropic-0159`

Snippet: `samples/flt-anthropic/flt-anthropic-0159.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.qExpGens`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_MTorsionDiff.lean#L17-L20) — `flt-anthropic-0160`

Snippet: `samples/flt-anthropic/flt-anthropic-0160.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange.ModularCurve.AHBridge.qe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_qExpansion_div_mem_laurentBaseChange.lean#L55-L56) — `flt-anthropic-0161`

Snippet: `samples/flt-anthropic/flt-anthropic-0161.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.R4F4aEd2.gzero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.lean#L486-L487) — `flt-anthropic-0162`

Snippet: `samples/flt-anthropic/flt-anthropic-0162.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_alSlash_heckeT_comm.WcPort.CuspForm.atkinLehnerHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_alSlash_heckeT_comm.lean#L1420-L1424) — `flt-anthropic-0163`

Snippet: `samples/flt-anthropic/flt-anthropic-0163.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq.ModularCurve.ARails.etaL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_E4_mul_eta_pow_eight_eq.lean#L159-L159) — `flt-anthropic-0164`

Snippet: `samples/flt-anthropic/flt-anthropic-0164.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux.π₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.lean#L31-L31) — `flt-anthropic-0165`

Snippet: `samples/flt-anthropic/flt-anthropic-0165.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_dvd.QCDdvd.algAlongBeta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_dvd.lean#L220-L221) — `flt-anthropic-0166`

Snippet: `samples/flt-anthropic/flt-anthropic-0166.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Rep.dimShiftDownSC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GroupCohomology_TateDimensionShiftMaps.lean#L62-L67) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq.CTap.LiesOverVal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq.lean#L22-L23) — `flt-anthropic-0168`

Snippet: `samples/flt-anthropic/flt-anthropic-0168.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2.K42CT.corrEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2.lean#L473-L492) — `flt-anthropic-0169`

Snippet: `samples/flt-anthropic/flt-anthropic-0169.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul.KcEpsteinTail.Z`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul.lean#L75-L76) — `flt-anthropic-0170`

Snippet: `samples/flt-anthropic/flt-anthropic-0170.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd.OccupancyDvdSol.wL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd.lean#L274-L276) — `flt-anthropic-0171`

Snippet: `samples/flt-anthropic/flt-anthropic-0171.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiMain.unitVal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.lean#L337-L339) — `flt-anthropic-0172`

Snippet: `samples/flt-anthropic/flt-anthropic-0172.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.HeckeCharacter.placeOrd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LT_HeckeChar_exists_heckeCharOfRayClassChar.lean#L34-L35) — `flt-anthropic-0173`

Snippet: `samples/flt-anthropic/flt-anthropic-0173.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler.lean#L363-L366) — `flt-anthropic-0174`

Snippet: `samples/flt-anthropic/flt-anthropic-0174.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom.R4GC.stretch`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom.lean#L2187-L2188) — `flt-anthropic-0175`

Snippet: `samples/flt-anthropic/flt-anthropic-0175.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants.P2mSWSndLeg.StdStable`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants.lean#L93-L95) — `flt-anthropic-0176`

Snippet: `samples/flt-anthropic/flt-anthropic-0176.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`DrinfeldCurve.LocalChart.ChartPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_DrinfeldCurve_LocalChart.lean#L21-L27) — `flt-anthropic-0177`

Snippet: `samples/flt-anthropic/flt-anthropic-0177.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.RQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.lean#L21-L21) — `flt-anthropic-0178`

Snippet: `samples/flt-anthropic/flt-anthropic-0178.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`WeierstrassCurve.cusp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_EDSEngine.lean#L1116-L1116) — `flt-anthropic-0179`

Snippet: `samples/flt-anthropic/flt-anthropic-0179.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct.TorusFamilyK.optMeas`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct.lean#L46-L48) — `flt-anthropic-0180`

Snippet: `samples/flt-anthropic/flt-anthropic-0180.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.AlgebraicCurve.CFEFibre.αv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.lean#L432-L434) — `flt-anthropic-0181`

Snippet: `samples/flt-anthropic/flt-anthropic-0181.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub.AutomorphicForm.GL2RealPrincipalSeriesModel.cL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub.lean#L38-L38) — `flt-anthropic-0182`

Snippet: `samples/flt-anthropic/flt-anthropic-0182.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.fppfH0SectionsIsoApp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FppfH0Identification.lean#L112-L117) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.levelComponentField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_LevelFunctionField.lean#L198-L201) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin.WGenC.prodMapIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin.lean#L313-L330) — `flt-anthropic-0185`

Snippet: `samples/flt-anthropic/flt-anthropic-0185.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.K2Core.ch`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.lean#L349-L349) — `flt-anthropic-0186`

Snippet: `samples/flt-anthropic/flt-anthropic-0186.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.PV1TL.κiso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.lean#L300-L303) — `flt-anthropic-0187`

Snippet: `samples/flt-anthropic/flt-anthropic-0187.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry.RelPicard.HomNu2Aux.Phi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.lean#L153-L155) — `flt-anthropic-0188`

Snippet: `samples/flt-anthropic/flt-anthropic-0188.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero.SelbergPGL.adMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero.lean#L31-L32) — `flt-anthropic-0189`

Snippet: `samples/flt-anthropic/flt-anthropic-0189.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.ell`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L16-L16) — `flt-anthropic-0190`

Snippet: `samples/flt-anthropic/flt-anthropic-0190.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve.OmegaGammaHCharZeroProof.restrictCusp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.lean#L290-L295) — `flt-anthropic-0191`

Snippet: `samples/flt-anthropic/flt-anthropic-0191.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian.LevelL3.torsLift`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.lean#L82-L84) — `flt-anthropic-0192`

Snippet: `samples/flt-anthropic/flt-anthropic-0192.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.DeligneSerreL49G.spec`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.lean#L354-L355) — `flt-anthropic-0193`

Snippet: `samples/flt-anthropic/flt-anthropic-0193.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent.T2Aux.ev`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent.lean#L197-L198) — `flt-anthropic-0194`

Snippet: `samples/flt-anthropic/flt-anthropic-0194.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.P2mMumfordKerModel.φ₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.lean#L142-L142) — `flt-anthropic-0195`

Snippet: `samples/flt-anthropic/flt-anthropic-0195.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_map_act_add_mumfordBundle_iso_tensor.LambdaSymbol29.pt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_map_act_add_mumfordBundle_iso_tensor.lean#L204-L204) — `flt-anthropic-0196`

Snippet: `samples/flt-anthropic/flt-anthropic-0196.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_AuxLevel_finrank_midML_le_two_mul_finrank_baseML.MidRankSol.instIsLocW₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_AuxLevel_finrank_midML_le_two_mul_finrank_baseML.lean#L252-L254) — `flt-anthropic-0197`

Snippet: `samples/flt-anthropic/flt-anthropic-0197.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule.ThetaDescentAux.prodCover`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule.lean#L46-L47) — `flt-anthropic-0198`

Snippet: `samples/flt-anthropic/flt-anthropic-0198.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor.toLoc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean#L478-L479) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC.shp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.lean#L53-L56) — `flt-anthropic-0200`

Snippet: `samples/flt-anthropic/flt-anthropic-0200.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf.ModularCurve.UVCrossingModel.nfV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf.lean#L2174-L2176) — `flt-anthropic-0201`

Snippet: `samples/flt-anthropic/flt-anthropic-0201.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.AlgebraicGeometry.RelPicard.K7cov35.fibreIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.lean#L127-L128) — `flt-anthropic-0202`

Snippet: `samples/flt-anthropic/flt-anthropic-0202.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.mkV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.lean#L479-L479) — `flt-anthropic-0203`

Snippet: `samples/flt-anthropic/flt-anthropic-0203.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.InertAssembly.sA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.lean#L828-L834) — `flt-anthropic-0204`

Snippet: `samples/flt-anthropic/flt-anthropic-0204.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisEven.vm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean#L356-L356) — `flt-anthropic-0205`

Snippet: `samples/flt-anthropic/flt-anthropic-0205.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.jLinePlaceZero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_JLinePlaces.lean#L54-L56) — `flt-anthropic-0206`

Snippet: `samples/flt-anthropic/flt-anthropic-0206.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero.GoodReductionJacobian.RelativeGroupLaw.kwPairingMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero.lean#L182-L183) — `flt-anthropic-0207`

Snippet: `samples/flt-anthropic/flt-anthropic-0207.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_eq_integral_weylIntertwiningIntegral_mul_conj_of_re_gt_half.R4AdjW.P0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_eq_integral_weylIntertwiningIntegral_mul_conj_of_re_gt_half.lean#L295-L295) — `flt-anthropic-0208`

Snippet: `samples/flt-anthropic/flt-anthropic-0208.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR.ι`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.lean#L905-L906) — `flt-anthropic-0209`

Snippet: `samples/flt-anthropic/flt-anthropic-0209.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_iff_of_translate_corr_of_isAlgClosed_heightNormalised_eq_oneLeg.G3C3.comapExtraLevel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_iff_of_translate_corr_of_isAlgClosed_heightNormalised_eq_oneLeg.lean#L93-L149) — `flt-anthropic-0210`

Snippet: `samples/flt-anthropic/flt-anthropic-0210.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_heckeInputsHAlong.HeckeInputsHAll.levelRaise`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean#L125-L129) — `flt-anthropic-0211`

Snippet: `samples/flt-anthropic/flt-anthropic-0211.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.CSTower.degVShift`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.lean#L1069-L1070) — `flt-anthropic-0212`

Snippet: `samples/flt-anthropic/flt-anthropic-0212.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC.GenHSol.An`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC.lean#L254-L254) — `flt-anthropic-0213`

Snippet: `samples/flt-anthropic/flt-anthropic-0213.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart.L2Box46.Φb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart.lean#L498-L498) — `flt-anthropic-0214`

Snippet: `samples/flt-anthropic/flt-anthropic-0214.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.KcConjType.Hm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.lean#L361-L362) — `flt-anthropic-0215`

Snippet: `samples/flt-anthropic/flt-anthropic-0215.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation.LigozatUnitBar.uInvA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation.lean#L172-L172) — `flt-anthropic-0216`

Snippet: `samples/flt-anthropic/flt-anthropic-0216.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le.TruncBCEngine.xfam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le.lean#L228-L230) — `flt-anthropic-0217`

Snippet: `samples/flt-anthropic/flt-anthropic-0217.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span.TwoCuspLatticeAlg.intSub`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span.lean#L27-L38) — `flt-anthropic-0218`

Snippet: `samples/flt-anthropic/flt-anthropic-0218.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers.PDivDAlphaK.OR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers.lean#L345-L346) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow.ADT.kap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow.lean#L84-L84) — `flt-anthropic-0220`

Snippet: `samples/flt-anthropic/flt-anthropic-0220.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.KeyLeftSkel.baseV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.lean#L156-L158) — `flt-anthropic-0221`

Snippet: `samples/flt-anthropic/flt-anthropic-0221.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring.WeierstrassCurve.DualExist.Pt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring.lean#L254-L254) — `flt-anthropic-0222`

Snippet: `samples/flt-anthropic/flt-anthropic-0222.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve.JHNeronObjectAtP.RedLambda.redHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.lean#L259-L264) — `flt-anthropic-0223`

Snippet: `samples/flt-anthropic/flt-anthropic-0223.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.J1ThirteenPlaneModel.J1ThirteenPicZeroFibreDiamond.J1ThirteenPicZeroLiteralChordChain.J1ThirteenPicZeroPlaceDictionary.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction.J1ThirteenPicZeroLitPic0Comparison.J1ThirteenX113RiemannRochRows.MazurTate1973Mt31b.J1ThirteenX113PackageHeldRowOne.MilneAvAg9bRd9DictionaryHeld3Closure.J1ThirteenX113OrdRowWellDefinedReduction.MilneAvAg9bRd10EllKFinUpperRow.MilneAvAg9bRd11X113TowerPowerBasis.Ag9b11bX113HwdUnitDischarge.MilneAvAg9bRd11DictionaryBinderShrink.MilneAvAg9bRd12X113AssemblyRetirement.MilneAvAg9bRd12T1P1InftyResidue.MilneAvAg9bRd12X113LocalDatumMint.MilneAvAg9bRd12X113FiveRowUpgrade.AlgebraicCurve.Place.toValuationSubringOfRestrictEq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean#L3931-L3934) — `flt-anthropic-0224`

Snippet: `samples/flt-anthropic/flt-anthropic-0224.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.RelPicard.BaseTransport.BaseChange.ofR_mapIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RigKerDualNumberBaseTransport.lean#L96-L99) — `flt-anthropic-0225`

Snippet: `samples/flt-anthropic/flt-anthropic-0225.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.S17C1.Nc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.lean#L112-L112) — `flt-anthropic-0226`

Snippet: `samples/flt-anthropic/flt-anthropic-0226.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer.CCountsN.ModQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer.lean#L767-L767) — `flt-anthropic-0227`

Snippet: `samples/flt-anthropic/flt-anthropic-0227.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`GaloisRepAdic.ofResidualGaloisRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GaloisRep_Adic.lean#L196-L205) — `flt-anthropic-0228`

Snippet: `samples/flt-anthropic/flt-anthropic-0228.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.toTJ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.lean#L546-L547) — `flt-anthropic-0229`

Snippet: `samples/flt-anthropic/flt-anthropic-0229.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.X1aRed.bc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.lean#L147-L149) — `flt-anthropic-0230`

Snippet: `samples/flt-anthropic/flt-anthropic-0230.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring.MatrixUnitsRebase.f`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring.lean#L53-L54) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.W1ISO.en`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.lean#L215-L215) — `flt-anthropic-0232`

Snippet: `samples/flt-anthropic/flt-anthropic-0232.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve.GreenSidePairing.Φt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.lean#L353-L353) — `flt-anthropic-0233`

Snippet: `samples/flt-anthropic/flt-anthropic-0233.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul.KcSemiLocalSigmaLinGen.μ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul.lean#L111-L111) — `flt-anthropic-0234`

Snippet: `samples/flt-anthropic/flt-anthropic-0234.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar.RFConst.res'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar.lean#L21-L21) — `flt-anthropic-0235`

Snippet: `samples/flt-anthropic/flt-anthropic-0235.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le.CompactPictureLowering.P3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le.lean#L14-L14) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve.RationalHomUnits.substXY`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_finite_rationalHomSet_units.lean#L22-L23) — `flt-anthropic-0237`

Snippet: `samples/flt-anthropic/flt-anthropic-0237.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.pot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean#L424-L424) — `flt-anthropic-0238`

Snippet: `samples/flt-anthropic/flt-anthropic-0238.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv.U`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.lean#L259-L259) — `flt-anthropic-0239`

Snippet: `samples/flt-anthropic/flt-anthropic-0239.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.toH1Aux`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_CechSectionsOfDivisor.lean#L233-L235) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.CubicInduction.translateRepStep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_CubicInduction_AdditiveJacquet.lean#L54-L63) — `flt-anthropic-0241`

Snippet: `samples/flt-anthropic/flt-anthropic-0241.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_alSlash_heckeT_comm.WcPort.ModularCurve.ALData.traceRepMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_alSlash_heckeT_comm.lean#L1473-L1475) — `flt-anthropic-0242`

Snippet: `samples/flt-anthropic/flt-anthropic-0242.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve.FF4.E`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.lean#L40-L40) — `flt-anthropic-0243`

Snippet: `samples/flt-anthropic/flt-anthropic-0243.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NeronSpecialFibreInfra.fibreRestrictAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_NeronSpecialFibreRestriction.lean#L41-L45) — `flt-anthropic-0244`

Snippet: `samples/flt-anthropic/flt-anthropic-0244.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero.IdAff.DData.gen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero.lean#L125-L125) — `flt-anthropic-0245`

Snippet: `samples/flt-anthropic/flt-anthropic-0245.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero.KTORDBeta.ζ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero.lean#L447-L447) — `flt-anthropic-0246`

Snippet: `samples/flt-anthropic/flt-anthropic-0246.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.P2MKcCQJbc.ptMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean#L13-L16) — `flt-anthropic-0247`

Snippet: `samples/flt-anthropic/flt-anthropic-0247.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_perfectPairing_antisymm_cornerSubmodule_H1_of_not_isEisenstein.CohCarrier.CornerDual.rat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_perfectPairing_antisymm_cornerSubmodule_H1_of_not_isEisenstein.lean#L352-L352) — `flt-anthropic-0248`

Snippet: `samples/flt-anthropic/flt-anthropic-0248.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch.GenPairH.ι₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch.lean#L90-L90) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_LambdaModularPolynomialData_psi_reciprocal.LambdaRecipSol.Fμ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_LambdaModularPolynomialData_psi_reciprocal.lean#L89-L89) — `flt-anthropic-0250`

Snippet: `samples/flt-anthropic/flt-anthropic-0250.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Deformation.repnQuotFunctor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Deformations_LiftFunctor.lean#L36-L54) — `flt-anthropic-0251`

Snippet: `samples/flt-anthropic/flt-anthropic-0251.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.SymRestriction.admQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.lean#L361-L361) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm.ModularCurve.PDPairing.BaseTwo.rep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_heckeT0_comm.lean#L2008-L2008) — `flt-anthropic-0253`

Snippet: `samples/flt-anthropic/flt-anthropic-0253.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.ArchBorelCoord.psiG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.lean#L122-L123) — `flt-anthropic-0254`

Snippet: `samples/flt-anthropic/flt-anthropic-0254.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one.L5G.genRestrict`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one.lean#L239-L243) — `flt-anthropic-0255`

Snippet: `samples/flt-anthropic/flt-anthropic-0255.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.ToricHeckeAlg.evHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.lean#L35-L38) — `flt-anthropic-0256`

Snippet: `samples/flt-anthropic/flt-anthropic-0256.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.OModulePresheaf.tensor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_OModulePresheafTensor.lean#L48-L74) — `flt-anthropic-0257`

Snippet: `samples/flt-anthropic/flt-anthropic-0257.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_localChar_eq_one_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel_of_valued_sub_one_le.PSUnramN.unitOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_localChar_eq_one_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel_of_valued_sub_one_le.lean#L261-L266) — `flt-anthropic-0258`

Snippet: `samples/flt-anthropic/flt-anthropic-0258.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.SymmetricPowerPackage`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_SymmetricPower.lean#L93-L126) — `flt-anthropic-0259`

Snippet: `samples/flt-anthropic/flt-anthropic-0259.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.ModularCurve.BilinearUnfolded.mob`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.lean#L39-L39) — `flt-anthropic-0260`

Snippet: `samples/flt-anthropic/flt-anthropic-0260.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.AlgebraicGeometry.OModulePresheaf.Rebase.σ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.lean#L325-L325) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ.SlSph.wK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ.lean#L31-L34) — `flt-anthropic-0262`

Snippet: `samples/flt-anthropic/flt-anthropic-0262.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable.selE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.lean#L313-L314) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PeriodPair_jLattice_surjective.ModularCurve.kwQepw123c_jH`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PeriodPair_jLattice_surjective.lean#L525-L526) — `flt-anthropic-0264`

Snippet: `samples/flt-anthropic/flt-anthropic-0264.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits.P2mUnramifiedSemiLocalCharacter.phi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits.lean#L89-L93) — `flt-anthropic-0265`

Snippet: `samples/flt-anthropic/flt-anthropic-0265.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle.KcDescEff.FF`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle.lean#L20-L20) — `flt-anthropic-0266`

Snippet: `samples/flt-anthropic/flt-anthropic-0266.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.EDB.tr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.lean#L83-L84) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice.AutomorphicForm.GL2Real.RHead.Jint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice.lean#L1155-L1157) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal.ZeroSchemeBC.triv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal.lean#L460-L469) — `flt-anthropic-0269`

Snippet: `samples/flt-anthropic/flt-anthropic-0269.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso.L3Sol.invT`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso.lean#L40-L40) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit.ToricReadAsm.NodeDatum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit.lean#L333-L333) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator.IsoHom16.IsHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator.lean#L38-L41) — `flt-anthropic-0272`

Snippet: `samples/flt-anthropic/flt-anthropic-0272.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.FinFlatHopf.W4.Nadd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.lean#L1240-L1242) — `flt-anthropic-0273`

Snippet: `samples/flt-anthropic/flt-anthropic-0273.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.pr₂`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.lean#L182-L189) — `flt-anthropic-0274`

Snippet: `samples/flt-anthropic/flt-anthropic-0274.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_eichlerShimura_H1_top.ESCompA.transport`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_eichlerShimura_H1_top.lean#L45-L59) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc.AlgebraicCurve.AlgebraicCurve.RationalFunctionField.riemannRochSpaceEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc.lean#L440-L450) — `flt-anthropic-0276`

Snippet: `samples/flt-anthropic/flt-anthropic-0276.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`WeierstrassCurve.Affine.Point.NetPairingNondegenerate`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NetPairing_Basic.lean#L94-L97) — `flt-anthropic-0277`

Snippet: `samples/flt-anthropic/flt-anthropic-0277.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_slabForm.MemB48.archHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_smoothingModule_slabForm.lean#L374-L375) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean#L410-L411) — `flt-anthropic-0279`

Snippet: `samples/flt-anthropic/flt-anthropic-0279.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.RingHom.CasimirLiftAux.IsCasimir`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.lean#L18-L19) — `flt-anthropic-0280`

Snippet: `samples/flt-anthropic/flt-anthropic-0280.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile.K7RA5.Φ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile.lean#L23-L23) — `flt-anthropic-0281`

Snippet: `samples/flt-anthropic/flt-anthropic-0281.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA.SLq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.lean#L136-L136) — `flt-anthropic-0282`

Snippet: `samples/flt-anthropic/flt-anthropic-0282.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset.LanglandsTunnell.CubicInduction.ArchConvCalculus.liftE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset.lean#L82-L83) — `flt-anthropic-0283`

Snippet: `samples/flt-anthropic/flt-anthropic-0283.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.M4aHerbrand.TowerPkgProof.βU`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.lean#L147-L147) — `flt-anthropic-0284`

Snippet: `samples/flt-anthropic/flt-anthropic-0284.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.lean#L178-L178) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic.L0aSKit.foldrTwistCongr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic.lean#L99-L103) — `flt-anthropic-0286`

Snippet: `samples/flt-anthropic/flt-anthropic-0286.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale.LevelFibreBody.ΓC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale.lean#L20-L20) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction.MilneL43.OD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.lean#L521-L521) — `flt-anthropic-0288`

Snippet: `samples/flt-anthropic/flt-anthropic-0288.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.WZE.E1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean#L574-L574) — `flt-anthropic-0289`

Snippet: `samples/flt-anthropic/flt-anthropic-0289.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.JpssD4KubotaFiniteAdelicProductObjectSlice.jpd4r17t5_oddComplementProduct`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean#L4747-L4748) — `flt-anthropic-0290`

Snippet: `samples/flt-anthropic/flt-anthropic-0290.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.inApp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.lean#L842-L850) — `flt-anthropic-0291`

Snippet: `samples/flt-anthropic/flt-anthropic-0291.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker.FGH1.ιB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker.lean#L109-L109) — `flt-anthropic-0292`

Snippet: `samples/flt-anthropic/flt-anthropic-0292.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_le_add_sub_natCard_of_isInvertible.AlgebraicGeometry.TwoGluedCurves.ChiE31.app1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_le_add_sub_natCard_of_isInvertible.lean#L804-L805) — `flt-anthropic-0293`

Snippet: `samples/flt-anthropic/flt-anthropic-0293.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.LBA.convInv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.lean#L77-L78) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle.BiRigidify.unit_of_tensor_unit`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle.lean#L40-L41) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue.locEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.lean#L40-L42) — `flt-anthropic-0296`

Snippet: `samples/flt-anthropic/flt-anthropic-0296.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul.A2FRHG.ΓGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul.lean#L28-L29) — `flt-anthropic-0297`

Snippet: `samples/flt-anthropic/flt-anthropic-0297.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_periodMap_heckeULin.ModularCurve.Period.SolHeckeU.HeckeAnalytic.repGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_periodMap_heckeULin.lean#L97-L102) — `flt-anthropic-0298`

Snippet: `samples/flt-anthropic/flt-anthropic-0298.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2.AlgebraicGeometry.AlgebraicGeometry.P2mWs3V2piBridge.tensorPowIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2.lean#L254-L256) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.prSnd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.lean#L174-L175) — `flt-anthropic-0300`

Snippet: `samples/flt-anthropic/flt-anthropic-0300.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm.IwasawaCoord.LHaar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean#L171-L171) — `flt-anthropic-0301`

Snippet: `samples/flt-anthropic/flt-anthropic-0301.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback.S2Mul.P₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback.lean#L90-L91) — `flt-anthropic-0302`

Snippet: `samples/flt-anthropic/flt-anthropic-0302.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis.R2CompTT.SS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean#L403-L404) — `flt-anthropic-0303`

Snippet: `samples/flt-anthropic/flt-anthropic-0303.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.PhiGen.cosetB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_PhiGen.lean#L206-L206) — `flt-anthropic-0304`

Snippet: `samples/flt-anthropic/flt-anthropic-0304.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul.AnnulusUnif.ψ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul.lean#L242-L250) — `flt-anthropic-0305`

Snippet: `samples/flt-anthropic/flt-anthropic-0305.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`HomogeneousIdealQuotientGrading.quotDecompose`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra.lean#L100-L103) — `flt-anthropic-0306`

Snippet: `samples/flt-anthropic/flt-anthropic-0306.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle.P2mOneParam.U`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle.lean#L241-L241) — `flt-anthropic-0307`

Snippet: `samples/flt-anthropic/flt-anthropic-0307.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.finFibrePow.permHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_SymmetricPower.lean#L29-L30) — `flt-anthropic-0308`

Snippet: `samples/flt-anthropic/flt-anthropic-0308.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.Ws47.CB3.thetaₗ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.lean#L56-L59) — `flt-anthropic-0309`

Snippet: `samples/flt-anthropic/flt-anthropic-0309.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.ModularCurve.DResBarBody.toRingAutHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.lean#L43-L46) — `flt-anthropic-0310`

Snippet: `samples/flt-anthropic/flt-anthropic-0310.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.ssNodePairsQExp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_XHDifferentialsModL.lean#L307-L308) — `flt-anthropic-0311`

Snippet: `samples/flt-anthropic/flt-anthropic-0311.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.RelPicard.constDiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RelPicardAbelJacobiFamily.lean#L104-L105) — `flt-anthropic-0312`

Snippet: `samples/flt-anthropic/flt-anthropic-0312.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv.E0Aux.conjD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv.lean#L356-L363) — `flt-anthropic-0313`

Snippet: `samples/flt-anthropic/flt-anthropic-0313.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm.TwistedOrbitalEuler.sMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.lean#L250-L252) — `flt-anthropic-0314`

Snippet: `samples/flt-anthropic/flt-anthropic-0314.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule.WsB.T2.realM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule.lean#L36-L36) — `flt-anthropic-0315`

Snippet: `samples/flt-anthropic/flt-anthropic-0315.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_induced_binaryFormRepSL_top.HeckeEis.UH3Sol.Vn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_induced_binaryFormRepSL_top.lean#L27-L27) — `flt-anthropic-0316`

Snippet: `samples/flt-anthropic/flt-anthropic-0316.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_AuxLevel_finrank_midML_le_two_mul_finrank_baseML.MidRankSol.linearMapOfX`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_AuxLevel_finrank_midML_le_two_mul_finrank_baseML.lean#L85-L92) — `flt-anthropic-0317`

Snippet: `samples/flt-anthropic/flt-anthropic-0317.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD.xOfCotangentHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.lean#L671-L687) — `flt-anthropic-0318`

Snippet: `samples/flt-anthropic/flt-anthropic-0318.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero.IdAff.DData.U`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero.lean#L91-L91) — `flt-anthropic-0319`

Snippet: `samples/flt-anthropic/flt-anthropic-0319.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE.jL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.lean#L1673-L1675) — `flt-anthropic-0320`

Snippet: `samples/flt-anthropic/flt-anthropic-0320.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le.EndVertex.swapInv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le.lean#L675-L682) — `flt-anthropic-0321`

Snippet: `samples/flt-anthropic/flt-anthropic-0321.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_red_ne_zero_and_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits_of_isStrictTypeOne.ModularCurve.N1Glue.deltaSeriesZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_red_ne_zero_and_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits_of_isStrictTypeOne.lean#L116-L117) — `flt-anthropic-0322`

Snippet: `samples/flt-anthropic/flt-anthropic-0322.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite.LevelAverageFinSol.Ctx.dm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite.lean#L409-L409) — `flt-anthropic-0323`

Snippet: `samples/flt-anthropic/flt-anthropic-0323.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.kd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.lean#L489-L491) — `flt-anthropic-0324`

Snippet: `samples/flt-anthropic/flt-anthropic-0324.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.R4GC.GH`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean#L1174-L1174) — `flt-anthropic-0325`

Snippet: `samples/flt-anthropic/flt-anthropic-0325.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare.KcEllOrbUnfold.Λ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare.lean#L542-L542) — `flt-anthropic-0326`

Snippet: `samples/flt-anthropic/flt-anthropic-0326.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable.P6B.shellIdx`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable.lean#L6206-L6210) — `flt-anthropic-0327`

Snippet: `samples/flt-anthropic/flt-anthropic-0327.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab.cOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.lean#L44-L44) — `flt-anthropic-0328`

Snippet: `samples/flt-anthropic/flt-anthropic-0328.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.AdicCompletion.ComplFiniteAux.idx`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.lean#L106-L109) — `flt-anthropic-0329`

Snippet: `samples/flt-anthropic/flt-anthropic-0329.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible.AlgebraicGeometry.AlgebraicGeometry.RelPicard.G2.fibreModuleIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible.lean#L640-L645) — `flt-anthropic-0330`

Snippet: `samples/flt-anthropic/flt-anthropic-0330.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.ToricCountSol.CutConnected`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean#L45-L46) — `flt-anthropic-0331`

Snippet: `samples/flt-anthropic/flt-anthropic-0331.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint.LBShared.red`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint.lean#L69-L70) — `flt-anthropic-0332`

Snippet: `samples/flt-anthropic/flt-anthropic-0332.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank.M4aLocalCFT.HerbrandPair.ofAddAut`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank.lean#L696-L716) — `flt-anthropic-0333`

Snippet: `samples/flt-anthropic/flt-anthropic-0333.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one.P2MW1cG.κ'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one.lean#L975-L975) — `flt-anthropic-0334`

Snippet: `samples/flt-anthropic/flt-anthropic-0334.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle.P2mKcBassSerreH1.Bb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle.lean#L393-L396) — `flt-anthropic-0335`

Snippet: `samples/flt-anthropic/flt-anthropic-0335.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.R4FoldCT.princEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.lean#L613-L613) — `flt-anthropic-0336`

Snippet: `samples/flt-anthropic/flt-anthropic-0336.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three.RootPow.pullbackTriple`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three.lean#L37-L40) — `flt-anthropic-0337`

Snippet: `samples/flt-anthropic/flt-anthropic-0337.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.LevelOneResidue.boxH`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.lean#L424-L424) — `flt-anthropic-0338`

Snippet: `samples/flt-anthropic/flt-anthropic-0338.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd.P2mS26Univ.PhiF0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd.lean#L1020-L1023) — `flt-anthropic-0339`

Snippet: `samples/flt-anthropic/flt-anthropic-0339.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.kerPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.lean#L234-L235) — `flt-anthropic-0340`

Snippet: `samples/flt-anthropic/flt-anthropic-0340.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.KwDyf2XiOrderBoundDecomp.kwDyf2_XiStripBound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean#L6494-L6497) — `flt-anthropic-0341`

Snippet: `samples/flt-anthropic/flt-anthropic-0341.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.P2mUnrFlat.TwFun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.lean#L170-L170) — `flt-anthropic-0342`

Snippet: `samples/flt-anthropic/flt-anthropic-0342.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles.M4aLocalCFT.FujisakiC2a.fiberCompact`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles.lean#L3677-L3678) — `flt-anthropic-0343`

Snippet: `samples/flt-anthropic/flt-anthropic-0343.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate.KwF4gRRTateCohenTateAgreement`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L2972-L2981) — `flt-anthropic-0344`

Snippet: `samples/flt-anthropic/flt-anthropic-0344.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.HilbertRecipPort.Iso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.lean#L13-L14) — `flt-anthropic-0345`

Snippet: `samples/flt-anthropic/flt-anthropic-0345.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius.CohCarrier.ESPar.BC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius.lean#L562-L570) — `flt-anthropic-0346`

Snippet: `samples/flt-anthropic/flt-anthropic-0346.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.jElin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.lean#L3692-L3706) — `flt-anthropic-0347`

Snippet: `samples/flt-anthropic/flt-anthropic-0347.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve.nuTwoFin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFormula_isNat.lean#L1016-L1017) — `flt-anthropic-0348`

Snippet: `samples/flt-anthropic/flt-anthropic-0348.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet.AutomorphicForm.LocalCofinite.Gt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet.lean#L34-L35) — `flt-anthropic-0349`

Snippet: `samples/flt-anthropic/flt-anthropic-0349.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.A2ALRat.kN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean#L65-L65) — `flt-anthropic-0350`

Snippet: `samples/flt-anthropic/flt-anthropic-0350.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_three_of_dvd.W1ISO.rhoE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_three_of_dvd.lean#L360-L360) — `flt-anthropic-0351`

Snippet: `samples/flt-anthropic/flt-anthropic-0351.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Rep_nonempty_iso_indBot_trivial_of_isPGroup.P2mS26K1.E`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Rep_nonempty_iso_indBot_trivial_of_isPGroup.lean#L93-L98) — `flt-anthropic-0352`

Snippet: `samples/flt-anthropic/flt-anthropic-0352.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner.μG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.lean#L36-L36) — `flt-anthropic-0353`

Snippet: `samples/flt-anthropic/flt-anthropic-0353.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ContinuousMulEquiv.units_map`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Mathlib_Topology_Algebra_ContinuousMonoidHom.lean#L39-L45) — `flt-anthropic-0354`

Snippet: `samples/flt-anthropic/flt-anthropic-0354.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_comp_one_pi.ModularCurve.DRModelPackageLevel.FrobLeg.Ygood`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_comp_one_pi.lean#L447-L449) — `flt-anthropic-0355`

Snippet: `samples/flt-anthropic/flt-anthropic-0355.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel.wA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.lean#L1978-L1979) — `flt-anthropic-0356`

Snippet: `samples/flt-anthropic/flt-anthropic-0356.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.TWLevel.HeckeRing.act`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CuspForm_TWLevelHeckeRing.lean#L183-L184) — `flt-anthropic-0357`

Snippet: `samples/flt-anthropic/flt-anthropic-0357.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`M4aHerbrand.GenuineDescent.genuineDescentOfTensorEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_M4aHerbrand_GenuineDescent.lean#L65-L71) — `flt-anthropic-0358`

Snippet: `samples/flt-anthropic/flt-anthropic-0358.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow.K2Tate.Tower.pr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow.lean#L661-L661) — `flt-anthropic-0359`

Snippet: `samples/flt-anthropic/flt-anthropic-0359.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.IsAttachedExact`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_IsAttached.lean#L15-L22) — `flt-anthropic-0360`

Snippet: `samples/flt-anthropic/flt-anthropic-0360.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_coeff_jNum_le_twelve.ModularCurve.JCoeff.LowCoeffs`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coeff_jNum_le_twelve.lean#L19-L20) — `flt-anthropic-0361`

Snippet: `samples/flt-anthropic/flt-anthropic-0361.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.ModularCurve.QExpN.RealL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean#L265-L266) — `flt-anthropic-0362`

Snippet: `samples/flt-anthropic/flt-anthropic-0362.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.RelPicard.rigSectionPullbackSndPullbackIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible.lean#L58-L62) — `flt-anthropic-0363`

Snippet: `samples/flt-anthropic/flt-anthropic-0363.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem.DescentK.Agen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem.lean#L303-L303) — `flt-anthropic-0364`

Snippet: `samples/flt-anthropic/flt-anthropic-0364.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_distribHaarChar_idelicNorm_genuineBaseChange.R2FafNAMod.actCAE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_distribHaarChar_idelicNorm_genuineBaseChange.lean#L190-L201) — `flt-anthropic-0365`

Snippet: `samples/flt-anthropic/flt-anthropic-0365.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_isPullback.ActKit19.bFam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_isPullback.lean#L977-L980) — `flt-anthropic-0366`

Snippet: `samples/flt-anthropic/flt-anthropic-0366.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_chartData_of_lineResidues.LineResidues.idxOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_chartData_of_lineResidues.lean#L658-L659) — `flt-anthropic-0367`

Snippet: `samples/flt-anthropic/flt-anthropic-0367.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal.Algebra.IsUnramifiedAt.CH2.localizationEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal.lean#L85-L91) — `flt-anthropic-0368`

Snippet: `samples/flt-anthropic/flt-anthropic-0368.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne.L1BUV.brHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne.lean#L16-L34) — `flt-anthropic-0369`

Snippet: `samples/flt-anthropic/flt-anthropic-0369.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.AlgebraicGeometry.RosenlichtL3.algU`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.lean#L146-L146) — `flt-anthropic-0370`

Snippet: `samples/flt-anthropic/flt-anthropic-0370.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.ComplexArchParam.trivialArtin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_ArchParam.lean#L121-L121) — `flt-anthropic-0371`

Snippet: `samples/flt-anthropic/flt-anthropic-0371.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible.TwoChartCech.GluedLinesModel.w₁'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible.lean#L236-L236) — `flt-anthropic-0372`

Snippet: `samples/flt-anthropic/flt-anthropic-0372.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback.ALBaseChange.img`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback.lean#L22-L25) — `flt-anthropic-0373`

Snippet: `samples/flt-anthropic/flt-anthropic-0373.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.UVCrossingModel.const`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_UVCrossingModel.lean#L29-L29) — `flt-anthropic-0374`

Snippet: `samples/flt-anthropic/flt-anthropic-0374.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel.CoeffNonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean#L437-L437) — `flt-anthropic-0375`

Snippet: `samples/flt-anthropic/flt-anthropic-0375.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.A2FRS.qExpSubmodule`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean#L182-L194) — `flt-anthropic-0376`

Snippet: `samples/flt-anthropic/flt-anthropic-0376.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage.onePt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.lean#L388-L390) — `flt-anthropic-0377`

Snippet: `samples/flt-anthropic/flt-anthropic-0377.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two.ModularCurve.FullLevel.K1Road.Jq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two.lean#L135-L136) — `flt-anthropic-0378`

Snippet: `samples/flt-anthropic/flt-anthropic-0378.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M.TadicPS.IsPointDerivation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.lean#L75-L76) — `flt-anthropic-0379`

Snippet: `samples/flt-anthropic/flt-anthropic-0379.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd.IgusaLevelDegDvd.Q`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd.lean#L575-L575) — `flt-anthropic-0380`

Snippet: `samples/flt-anthropic/flt-anthropic-0380.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.autOnPlaces`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_SSDegeneracyHecke.lean#L82-L84) — `flt-anthropic-0381`

Snippet: `samples/flt-anthropic/flt-anthropic-0381.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one.ValLtOneS8da.O`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one.lean#L188-L189) — `flt-anthropic-0382`

Snippet: `samples/flt-anthropic/flt-anthropic-0382.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three.P2MKcCEN3H.cycAct`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three.lean#L632-L632) — `flt-anthropic-0383`

Snippet: `samples/flt-anthropic/flt-anthropic-0383.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData.charted`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.lean#L297-L297) — `flt-anthropic-0384`

Snippet: `samples/flt-anthropic/flt-anthropic-0384.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.P2mSolLevelOneEsymm.zetaO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.lean#L515-L515) — `flt-anthropic-0385`

Snippet: `samples/flt-anthropic/flt-anthropic-0385.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.RelRepX.qmapO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.lean#L1617-L1625) — `flt-anthropic-0386`

Snippet: `samples/flt-anthropic/flt-anthropic-0386.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.ParInt.A`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.lean#L17-L17) — `flt-anthropic-0387`

Snippet: `samples/flt-anthropic/flt-anthropic-0387.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.IsTwist`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean#L49-L56) — `flt-anthropic-0388`

Snippet: `samples/flt-anthropic/flt-anthropic-0388.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.adjoinJq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_PhiGen.lean#L168-L168) — `flt-anthropic-0389`

Snippet: `samples/flt-anthropic/flt-anthropic-0389.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.AlgebraicGeometry.RelPicard.LFP.vtxHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.lean#L731-L734) — `flt-anthropic-0390`

Snippet: `samples/flt-anthropic/flt-anthropic-0390.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCSigma.Venue.ven`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean#L307-L322) — `flt-anthropic-0391`

Snippet: `samples/flt-anthropic/flt-anthropic-0391.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i.evalHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.lean#L466-L467) — `flt-anthropic-0392`

Snippet: `samples/flt-anthropic/flt-anthropic-0392.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt.R4GC.downSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt.lean#L1146-L1146) — `flt-anthropic-0393`

Snippet: `samples/flt-anthropic/flt-anthropic-0393.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0.INVOL.MF`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0.lean#L29-L29) — `flt-anthropic-0394`

Snippet: `samples/flt-anthropic/flt-anthropic-0394.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_forall_mem_cuspClasses_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule.AutomorphicForm.ArchCasimirScalarPrincipal.pins1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_forall_mem_cuspClasses_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule.lean#L106-L108) — `flt-anthropic-0395`

Snippet: `samples/flt-anthropic/flt-anthropic-0395.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25.split`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.lean#L181-L188) — `flt-anthropic-0396`

Snippet: `samples/flt-anthropic/flt-anthropic-0396.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq.HarmV0.repFinset`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq.lean#L124-L127) — `flt-anthropic-0397`

Snippet: `samples/flt-anthropic/flt-anthropic-0397.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd.NeronLeg1TwoBranches.transport`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd.lean#L280-L309) — `flt-anthropic-0398`

Snippet: `samples/flt-anthropic/flt-anthropic-0398.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic.WsB.C6.lower2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic.lean#L79-L80) — `flt-anthropic-0399`

Snippet: `samples/flt-anthropic/flt-anthropic-0399.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.α`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.lean#L101-L108) — `flt-anthropic-0400`

Snippet: `samples/flt-anthropic/flt-anthropic-0400.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AutomorphicForm.maximalCompactAwayHaar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean#L312-L312) — `flt-anthropic-0401`

Snippet: `samples/flt-anthropic/flt-anthropic-0401.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat.ArchNormalisedFactor.cplxNorm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat.lean#L5673-L5681) — `flt-anthropic-0402`

Snippet: `samples/flt-anthropic/flt-anthropic-0402.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom.W1xLA.ΦRingEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom.lean#L978-L982) — `flt-anthropic-0403`

Snippet: `samples/flt-anthropic/flt-anthropic-0403.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.RFFunct29.Mod.D`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.lean#L247-L249) — `flt-anthropic-0404`

Snippet: `samples/flt-anthropic/flt-anthropic-0404.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact.LevelNormal.IsPrincipalMatrix`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact.lean#L18-L20) — `flt-anthropic-0405`

Snippet: `samples/flt-anthropic/flt-anthropic-0405.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.WLight.R8cGlue.genPerm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean#L127-L139) — `flt-anthropic-0406`

Snippet: `samples/flt-anthropic/flt-anthropic-0406.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.AlgebraicGeometry.Scheme.Modules.exteriorPowerFreeIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.lean#L307-L313) — `flt-anthropic-0407`

Snippet: `samples/flt-anthropic/flt-anthropic-0407.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.EdgeData.sideOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_cellDissection.lean#L186-L188) — `flt-anthropic-0408`

Snippet: `samples/flt-anthropic/flt-anthropic-0408.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Deformation.DieudonneModule.verschiebung`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Dieudonne_WittHomColimit.lean#L317-L321) — `flt-anthropic-0409`

Snippet: `samples/flt-anthropic/flt-anthropic-0409.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.TateLocal.integersPositiveCompacts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_StandardLocalConstantsAt.lean#L102-L110) — `flt-anthropic-0410`

Snippet: `samples/flt-anthropic/flt-anthropic-0410.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange.AutomorphicForm.BaseChangeUnitSectionFn.pairGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange.lean#L389-L398) — `flt-anthropic-0411`

Snippet: `samples/flt-anthropic/flt-anthropic-0411.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away.GlueBody.locOne`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away.lean#L148-L149) — `flt-anthropic-0412`

Snippet: `samples/flt-anthropic/flt-anthropic-0412.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul.ResidualSplitting.quotColonEquivMapSpan`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul.lean#L88-L92) — `flt-anthropic-0413`

Snippet: `samples/flt-anthropic/flt-anthropic-0413.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve.genusFormulaNum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFormula_isNat.lean#L1076-L1078) — `flt-anthropic-0414`

Snippet: `samples/flt-anthropic/flt-anthropic-0414.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange.CerednikDrinfeld.BruhatTits.TransportPGL.pglMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange.lean#L33-L34) — `flt-anthropic-0415`

Snippet: `samples/flt-anthropic/flt-anthropic-0415.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det.TwistDataOn.chiDet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det.lean#L31-L31) — `flt-anthropic-0416`

Snippet: `samples/flt-anthropic/flt-anthropic-0416.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgFin_tensor.ModularCurve.IgusaScheme.jInv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgFin_tensor.lean#L131-L131) — `flt-anthropic-0417`

Snippet: `samples/flt-anthropic/flt-anthropic-0417.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one.HurTc.unitSphere`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one.lean#L61-L71) — `flt-anthropic-0418`

Snippet: `samples/flt-anthropic/flt-anthropic-0418.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_isHopfGalois_of_surjective.S17KT.T`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_isHopfGalois_of_surjective.lean#L36-L36) — `flt-anthropic-0419`

Snippet: `samples/flt-anthropic/flt-anthropic-0419.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.ChartDict3.degF`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.lean#L1883-L1887) — `flt-anthropic-0420`

Snippet: `samples/flt-anthropic/flt-anthropic-0420.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem.P2mWs19HorizNq.ιC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem.lean#L79-L81) — `flt-anthropic-0421`

Snippet: `samples/flt-anthropic/flt-anthropic-0421.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem.P2MKumE.HD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem.lean#L305-L305) — `flt-anthropic-0422`

Snippet: `samples/flt-anthropic/flt-anthropic-0422.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem.SatAsm.Naive`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem.lean#L41-L43) — `flt-anthropic-0423`

Snippet: `samples/flt-anthropic/flt-anthropic-0423.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit.PowerSeries.Submodule.IsIntegrallyClosed.COMP.sR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit.lean#L594-L594) — `flt-anthropic-0424`

Snippet: `samples/flt-anthropic/flt-anthropic-0424.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization.RowH.gIter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization.lean#L449-L452) — `flt-anthropic-0425`

Snippet: `samples/flt-anthropic/flt-anthropic-0425.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and.DDF2.scale`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and.lean#L21-L22) — `flt-anthropic-0426`

Snippet: `samples/flt-anthropic/flt-anthropic-0426.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd.M4aLocalCFT.HerbrandPair.restrictToSubgroup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd.lean#L10002-L10014) — `flt-anthropic-0427`

Snippet: `samples/flt-anthropic/flt-anthropic-0427.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt.Ws23.M3core.ptE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt.lean#L58-L59) — `flt-anthropic-0428`

Snippet: `samples/flt-anthropic/flt-anthropic-0428.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd.M4aHerbrand.sUnitCountHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd.lean#L9600-L9615) — `flt-anthropic-0429`

Snippet: `samples/flt-anthropic/flt-anthropic-0429.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve.WeierstrassCurve.reduceHomVS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_smul.lean#L1990-L1994) — `flt-anthropic-0430`

Snippet: `samples/flt-anthropic/flt-anthropic-0430.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit.LevEtaleCritBody.jC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit.lean#L98-L98) — `flt-anthropic-0431`

Snippet: `samples/flt-anthropic/flt-anthropic-0431.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.satIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.lean#L119-L145) — `flt-anthropic-0432`

Snippet: `samples/flt-anthropic/flt-anthropic-0432.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.WeierstrassCurve.B2a.vPull`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.lean#L105-L106) — `flt-anthropic-0433`

Snippet: `samples/flt-anthropic/flt-anthropic-0433.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_H1_of_not_isEisenstein.EscompD2.Λ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_H1_of_not_isEisenstein.lean#L462-L464) — `flt-anthropic-0434`

Snippet: `samples/flt-anthropic/flt-anthropic-0434.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.HopfAlgebra.FFHopfKerPID.φ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.lean#L51-L53) — `flt-anthropic-0435`

Snippet: `samples/flt-anthropic/flt-anthropic-0435.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.DimOneFibreAux.algPolyFib`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.lean#L29-L30) — `flt-anthropic-0436`

Snippet: `samples/flt-anthropic/flt-anthropic-0436.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LocalNewvector.padicK0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean#L158-L159) — `flt-anthropic-0437`

Snippet: `samples/flt-anthropic/flt-anthropic-0437.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_ptZ_eq_of_iso_of_isPullback_of_isPullback.G2PTZ.ePt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_ptZ_eq_of_iso_of_isPullback_of_isPullback.lean#L37-L38) — `flt-anthropic-0438`

Snippet: `samples/flt-anthropic/flt-anthropic-0438.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_isCyclic_and_natCard_dvd_sub_one_of_forall_comap_gauss_eq_of_forall_apply_eq_of_isLevelAutAt.W1xLA.ΦHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_isCyclic_and_natCard_dvd_sub_one_of_forall_comap_gauss_eq_of_forall_apply_eq_of_isLevelAutAt.lean#L954-L965) — `flt-anthropic-0439`

Snippet: `samples/flt-anthropic/flt-anthropic-0439.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_Etale_eq_of_forall_algHom_apply_eq.W2G9.homOfRangeLe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_Etale_eq_of_forall_algHom_apply_eq.lean#L163-L184) — `flt-anthropic-0440`

Snippet: `samples/flt-anthropic/flt-anthropic-0440.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein.RANKGH.Idx`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein.lean#L434-L434) — `flt-anthropic-0441`

Snippet: `samples/flt-anthropic/flt-anthropic-0441.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq.HasseDiv.S1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq.lean#L75-L75) — `flt-anthropic-0442`

Snippet: `samples/flt-anthropic/flt-anthropic-0442.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached.AlgebraicCurve.AlgebraicCurve.lSpaceShiftEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_omegaSpace_finite_of_genusReached.lean#L290-L322) — `flt-anthropic-0443`

Snippet: `samples/flt-anthropic/flt-anthropic-0443.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FinFlatHopf_exists_left_integral_frobenius.FinFlatHopf.S2.antipodeRepr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FinFlatHopf_exists_left_integral_frobenius.lean#L379-L384) — `flt-anthropic-0444`

Snippet: `samples/flt-anthropic/flt-anthropic-0444.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.wrLHS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L231-L232) — `flt-anthropic-0445`

Snippet: `samples/flt-anthropic/flt-anthropic-0445.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.ModularCurve.LevelN.QExpBridge.Phi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean#L872-L889) — `flt-anthropic-0446`

Snippet: `samples/flt-anthropic/flt-anthropic-0446.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam.ModularCurve.EIT.B'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam.lean#L291-L293) — `flt-anthropic-0447`

Snippet: `samples/flt-anthropic/flt-anthropic-0447.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit.KLICC.IsCoord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit.lean#L134-L141) — `flt-anthropic-0448`

Snippet: `samples/flt-anthropic/flt-anthropic-0448.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed.VeluOddSurjAux.N`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed.lean#L34-L36) — `flt-anthropic-0449`

Snippet: `samples/flt-anthropic/flt-anthropic-0449.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK.constantsHom'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing.lean#L107-L110) — `flt-anthropic-0450`

Snippet: `samples/flt-anthropic/flt-anthropic-0450.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient.EDB.L5RatRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient.lean#L642-L645) — `flt-anthropic-0451`

Snippet: `samples/flt-anthropic/flt-anthropic-0451.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite.L4Asm.pullbackCompIso'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite.lean#L102-L105) — `flt-anthropic-0452`

Snippet: `samples/flt-anthropic/flt-anthropic-0452.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension.ModularCurve.JZeroNeronObjectAtP.kerExt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronObjectAtP_exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension.lean#L630-L631) — `flt-anthropic-0453`

Snippet: `samples/flt-anthropic/flt-anthropic-0453.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift.KummerLift.fK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift.lean#L56-L57) — `flt-anthropic-0454`

Snippet: `samples/flt-anthropic/flt-anthropic-0454.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash.WcPort.SlashInvariantForm.atkinLehner`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_alSlash_add_heckeU_alSlash_alSlash.lean#L1343-L1346) — `flt-anthropic-0455`

Snippet: `samples/flt-anthropic/flt-anthropic-0455.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.W5b3G.cball`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.lean#L116-L116) — `flt-anthropic-0456`

Snippet: `samples/flt-anthropic/flt-anthropic-0456.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_tateAgreement_v2.ModularCurve.KwF4gRRTate.KwF4gRRTateCommFiniteGen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_tateAgreement_v2.lean#L2342-L2345) — `flt-anthropic-0457`

Snippet: `samples/flt-anthropic/flt-anthropic-0457.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.Reduce95.LamQ'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.lean#L2117-L2118) — `flt-anthropic-0458`

Snippet: `samples/flt-anthropic/flt-anthropic-0458.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.KleinFixedPointCount.Omega`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.lean#L16-L25) — `flt-anthropic-0459`

Snippet: `samples/flt-anthropic/flt-anthropic-0459.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp.C4Main.decimate`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp.lean#L23-L24) — `flt-anthropic-0460`

Snippet: `samples/flt-anthropic/flt-anthropic-0460.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized.jRingModularRangeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.lean#L481-L482) — `flt-anthropic-0461`

Snippet: `samples/flt-anthropic/flt-anthropic-0461.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2.BruhatCellHaar.cellMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2.lean#L306-L306) — `flt-anthropic-0462`

Snippet: `samples/flt-anthropic/flt-anthropic-0462.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve.QExpSplitField.lineAction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.lean#L936-L937) — `flt-anthropic-0463`

Snippet: `samples/flt-anthropic/flt-anthropic-0463.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable.FLT.EKAverage.ekAverageHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable.lean#L1775-L1784) — `flt-anthropic-0464`

Snippet: `samples/flt-anthropic/flt-anthropic-0464.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer.P2mKSpread.pullbackInvHomIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer.lean#L54-L57) — `flt-anthropic-0465`

Snippet: `samples/flt-anthropic/flt-anthropic-0465.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.PDivStep2R.tmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.lean#L468-L476) — `flt-anthropic-0466`

Snippet: `samples/flt-anthropic/flt-anthropic-0466.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.IharaTower.ResidualInjectivity.red`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.lean#L38-L39) — `flt-anthropic-0467`

Snippet: `samples/flt-anthropic/flt-anthropic-0467.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le.OrdCountAsm.iota`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le.lean#L441-L449) — `flt-anthropic-0468`

Snippet: `samples/flt-anthropic/flt-anthropic-0468.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_regularity_and_growth.MemReg48.HasExpansion`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_smoothingModule_regularity_and_growth.lean#L172-L180) — `flt-anthropic-0469`

Snippet: `samples/flt-anthropic/flt-anthropic-0469.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction.JacquetVanishing.repMid`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.lean#L42-L50) — `flt-anthropic-0470`

Snippet: `samples/flt-anthropic/flt-anthropic-0470.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE.dhat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_characterClosure_points_equiv.lean#L1127-L1127) — `flt-anthropic-0471`

Snippet: `samples/flt-anthropic/flt-anthropic-0471.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction.AlgebraicCurve.SpecializationPrincipleAux.compositeRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction.lean#L263-L325) — `flt-anthropic-0472`

Snippet: `samples/flt-anthropic/flt-anthropic-0472.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain.FiniteAdeleRing.Ws25E5.assocIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.lean#L129-L130) — `flt-anthropic-0473`

Snippet: `samples/flt-anthropic/flt-anthropic-0473.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.ModularCurve.sigma`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean#L125-L131) — `flt-anthropic-0474`

Snippet: `samples/flt-anthropic/flt-anthropic-0474.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap.B25TG.linB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap.lean#L93-L100) — `flt-anthropic-0475`

Snippet: `samples/flt-anthropic/flt-anthropic-0475.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model.intPolyToFin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.lean#L279-L280) — `flt-anthropic-0476`

Snippet: `samples/flt-anthropic/flt-anthropic-0476.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT.cRes`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.lean#L550-L551) — `flt-anthropic-0477`

Snippet: `samples/flt-anthropic/flt-anthropic-0477.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam.W`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.lean#L91-L91) — `flt-anthropic-0478`

Snippet: `samples/flt-anthropic/flt-anthropic-0478.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_finrank_coeffH1par_top_add_le.HeckeEis.UASol.eU`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_finrank_coeffH1par_top_add_le.lean#L24-L24) — `flt-anthropic-0479`

Snippet: `samples/flt-anthropic/flt-anthropic-0479.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg.AlgebraicCurve.PrimitiveAlongRegularPathProof.ChartCompatible`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg.lean#L139-L146) — `flt-anthropic-0480`

Snippet: `samples/flt-anthropic/flt-anthropic-0480.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall.shrinkPresheaf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.lean#L36-L41) — `flt-anthropic-0481`

Snippet: `samples/flt-anthropic/flt-anthropic-0481.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA.ιC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.lean#L612-L612) — `flt-anthropic-0482`

Snippet: `samples/flt-anthropic/flt-anthropic-0482.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules.ObjGlue.castComp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean#L788-L791) — `flt-anthropic-0483`

Snippet: `samples/flt-anthropic/flt-anthropic-0483.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two.ModularCurve.S2C.ratCurve`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two.lean#L1045-L1045) — `flt-anthropic-0484`

Snippet: `samples/flt-anthropic/flt-anthropic-0484.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.RegularProlongation.residueEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_ResidueDiscs.lean#L47-L48) — `flt-anthropic-0485`

Snippet: `samples/flt-anthropic/flt-anthropic-0485.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage.PkgDesc17.sAct'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage.lean#L623-L624) — `flt-anthropic-0486`

Snippet: `samples/flt-anthropic/flt-anthropic-0486.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top.OmegaGlueSol.glueLine`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top.lean#L72-L73) — `flt-anthropic-0487`

Snippet: `samples/flt-anthropic/flt-anthropic-0487.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_CosetGraph_exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder_of_level.Nat.placesOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_CosetGraph_exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder_of_level.lean#L83-L84) — `flt-anthropic-0488`

Snippet: `samples/flt-anthropic/flt-anthropic-0488.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.TwoChart.jInvChartInf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_TwoChartModel.lean#L143-L143) — `flt-anthropic-0489`

Snippet: `samples/flt-anthropic/flt-anthropic-0489.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`FppfRepresentableGroupSchemeSheaf.fppfOverAbelianSheaf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FppfGmRepresentable.lean#L201-L202) — `flt-anthropic-0490`

Snippet: `samples/flt-anthropic/flt-anthropic-0490.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A.uProd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.lean#L220-L221) — `flt-anthropic-0491`

Snippet: `samples/flt-anthropic/flt-anthropic-0491.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi.P2mS17E.evalAlgEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CartierDual_exists_algEquiv_monoidAlgebra_pi.lean#L73-L74) — `flt-anthropic-0492`

Snippet: `samples/flt-anthropic/flt-anthropic-0492.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.RelEffDivisor.pullbackAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_UniversalDivisor.lean#L96-L113) — `flt-anthropic-0493`

Snippet: `samples/flt-anthropic/flt-anthropic-0493.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.RankinSelberg.rs22Kernel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_RS22GlobalIntegral.lean#L79-L84) — `flt-anthropic-0494`

Snippet: `samples/flt-anthropic/flt-anthropic-0494.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two.K2Two.Ct₂`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two.lean#L831-L835) — `flt-anthropic-0495`

Snippet: `samples/flt-anthropic/flt-anthropic-0495.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.CellPeriods.γ'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.lean#L124-L124) — `flt-anthropic-0496`

Snippet: `samples/flt-anthropic/flt-anthropic-0496.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`closureTensorSpan`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FiniteFlat_ClosureHopf.lean#L30-L31) — `flt-anthropic-0497`

Snippet: `samples/flt-anthropic/flt-anthropic-0497.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry.HGPprimeImpl.comapCover`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.lean#L218-L225) — `flt-anthropic-0498`

Snippet: `samples/flt-anthropic/flt-anthropic-0498.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.G0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.lean#L537-L538) — `flt-anthropic-0499`

Snippet: `samples/flt-anthropic/flt-anthropic-0499.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.CSTower.unitGroup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.lean#L761-L762) — `flt-anthropic-0500`

Snippet: `samples/flt-anthropic/flt-anthropic-0500.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPlaneModel.J1ThirteenPicZeroFibreDiamond.J1ThirteenPicZeroLiteralChordChain.J1ThirteenPicZeroPlaceDictionary.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction.J1ThirteenPicZeroLitPic0Comparison.J1ThirteenX113RiemannRochRows.MazurTate1973Mt31b.J1ThirteenX113PackageHeldRowOne.MilneAvAg9bRd9DictionaryHeld3Closure.J1ThirteenX113OrdRowWellDefinedReduction.MilneAvAg9bRd10EllKFinUpperRow.MilneAvAg9bRd11X113TowerPowerBasis.Ag9b11bX113HwdUnitDischarge.MilneAvAg9bRd11DictionaryBinderShrink.MilneAvAg9bRd12X113AssemblyRetirement.MilneAvAg9bRd12T1P1InftyResidue.MilneAvAg9bRd12X113LocalDatumMint.MilneAvAg9bRd12X113FiveRowUpgrade.AlgebraicCurve.P1DifferentialCoeffUnitFinite`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L6772-L6773) — `flt-anthropic-0501`

Snippet: `samples/flt-anthropic/flt-anthropic-0501.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.siegelFun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_SiegelFunction.lean#L10-L17) — `flt-anthropic-0502`

Snippet: `samples/flt-anthropic/flt-anthropic-0502.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.ModularCurve.LevelN.QExpBridge.iotaM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean#L780-L781) — `flt-anthropic-0503`

Snippet: `samples/flt-anthropic/flt-anthropic-0503.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd.TwoGluedLinesBCAux.τSnd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd.lean#L467-L468) — `flt-anthropic-0504`

Snippet: `samples/flt-anthropic/flt-anthropic-0504.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.PeterssonCoset.pair`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CuspForm_PeterssonCoset.lean#L325-L326) — `flt-anthropic-0505`

Snippet: `samples/flt-anthropic/flt-anthropic-0505.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.R4RSUnfold.rep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.lean#L32-L34) — `flt-anthropic-0506`

Snippet: `samples/flt-anthropic/flt-anthropic-0506.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules.ObjGlue.proj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean#L578-L579) — `flt-anthropic-0507`

Snippet: `samples/flt-anthropic/flt-anthropic-0507.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a.OrbitCount.psi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.lean#L24-L32) — `flt-anthropic-0508`

Snippet: `samples/flt-anthropic/flt-anthropic-0508.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AddAut.mulLeft'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Compat_Mathlib430.lean#L202-L204) — `flt-anthropic-0509`

Snippet: `samples/flt-anthropic/flt-anthropic-0509.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase.W1xLA.sl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase.lean#L283-L285) — `flt-anthropic-0510`

Snippet: `samples/flt-anthropic/flt-anthropic-0510.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector.S17L2c.iL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector.lean#L36-L36) — `flt-anthropic-0511`

Snippet: `samples/flt-anthropic/flt-anthropic-0511.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NumberField.AdelicLevel.levelOne`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NumberField_AdelicLevel.lean#L589-L589) — `flt-anthropic-0512`

Snippet: `samples/flt-anthropic/flt-anthropic-0512.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`HeckeCohomology.IsTwist`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GroupCohomology_TransferHecke.lean#L12-L12) — `flt-anthropic-0513`

Snippet: `samples/flt-anthropic/flt-anthropic-0513.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.preGlue`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ModulesGlueOfCocycle.lean#L185-L193) — `flt-anthropic-0514`

Snippet: `samples/flt-anthropic/flt-anthropic-0514.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.ComponentChart.HasAffinoidLifting`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_AffinoidCentre.lean#L16-L21) — `flt-anthropic-0515`

Snippet: `samples/flt-anthropic/flt-anthropic-0515.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.TorusUnique.LRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.lean#L335-L337) — `flt-anthropic-0516`

Snippet: `samples/flt-anthropic/flt-anthropic-0516.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.AlgebraicGeometry.Scheme.Modules.piPowBicone`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.lean#L155-L171) — `flt-anthropic-0517`

Snippet: `samples/flt-anthropic/flt-anthropic-0517.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.QuatZeta.Emap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.lean#L464-L466) — `flt-anthropic-0518`

Snippet: `samples/flt-anthropic/flt-anthropic-0518.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit.comapIncl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.lean#L144-L149) — `flt-anthropic-0519`

Snippet: `samples/flt-anthropic/flt-anthropic-0519.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean#L36-L44) — `flt-anthropic-0520`

Snippet: `samples/flt-anthropic/flt-anthropic-0520.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Ihara.iharaAmalgam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_IharaAmalgam.lean#L17-L18) — `flt-anthropic-0521`

Snippet: `samples/flt-anthropic/flt-anthropic-0521.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq.F2AlphaE.unitK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq.lean#L243-L244) — `flt-anthropic-0522`

Snippet: `samples/flt-anthropic/flt-anthropic-0522.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing.IsProperOfProperClosedFibre.cmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing.lean#L79-L80) — `flt-anthropic-0523`

Snippet: `samples/flt-anthropic/flt-anthropic-0523.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Dock.cqEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.lean#L1112-L1123) — `flt-anthropic-0524`

Snippet: `samples/flt-anthropic/flt-anthropic-0524.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow.TruncatedDieudonneCount.I`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow.lean#L17-L17) — `flt-anthropic-0525`

Snippet: `samples/flt-anthropic/flt-anthropic-0525.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_orthFinite_and_archDeriv_mem.MemStab48.archHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_smoothingModule_orthFinite_and_archDeriv_mem.lean#L363-L364) — `flt-anthropic-0526`

Snippet: `samples/flt-anthropic/flt-anthropic-0526.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple.Ws23.Cover.unitF`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple.lean#L54-L54) — `flt-anthropic-0527`

Snippet: `samples/flt-anthropic/flt-anthropic-0527.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_PlaceDecomp_exists_faithful_bridge_isBase_isLocalFundamentalClass.NumberField.PlaceDecomp.FCFamily3b.BridgeFC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_PlaceDecomp_exists_faithful_bridge_isBase_isLocalFundamentalClass.lean#L119-L140) — `flt-anthropic-0528`

Snippet: `samples/flt-anthropic/flt-anthropic-0528.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.JHNeronObjectAtP.toricPoint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_JHNeronObjectAtP.lean#L218-L221) — `flt-anthropic-0529`

Snippet: `samples/flt-anthropic/flt-anthropic-0529.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd.P2mS26UnivA.gal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd.lean#L370-L374) — `flt-anthropic-0530`

Snippet: `samples/flt-anthropic/flt-anthropic-0530.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.HopfAlgebra.RaynaudConservative.comapIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.lean#L582-L582) — `flt-anthropic-0531`

Snippet: `samples/flt-anthropic/flt-anthropic-0531.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix.R4GC.upSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix.lean#L1136-L1136) — `flt-anthropic-0532`

Snippet: `samples/flt-anthropic/flt-anthropic-0532.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_NodalPic0_natCard_torsion_mul_pow_le_pow_of_isAlgClosed.NC.rep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_NodalPic0_natCard_torsion_mul_pow_le_pow_of_isAlgClosed.lean#L607-L609) — `flt-anthropic-0533`

Snippet: `samples/flt-anthropic/flt-anthropic-0533.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt.C8N.placeOfPrime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt.lean#L962-L963) — `flt-anthropic-0534`

Snippet: `samples/flt-anthropic/flt-anthropic-0534.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso.RigCocycle.Normalised`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso.lean#L316-L318) — `flt-anthropic-0535`

Snippet: `samples/flt-anthropic/flt-anthropic-0535.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc.evQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.lean#L746-L748) — `flt-anthropic-0536`

Snippet: `samples/flt-anthropic/flt-anthropic-0536.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.PlaceSpecialization.IsCuspidal'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_LevelOneProlongationPair.lean#L110-L116) — `flt-anthropic-0537`

Snippet: `samples/flt-anthropic/flt-anthropic-0537.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.Reduce95.hdiv'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.lean#L1848-L1850) — `flt-anthropic-0538`

Snippet: `samples/flt-anthropic/flt-anthropic-0538.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous.WsC.SplitAsm.gen₂`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous.lean#L45-L48) — `flt-anthropic-0539`

Snippet: `samples/flt-anthropic/flt-anthropic-0539.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.FormalOmega.coordToTensor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean#L75-L76) — `flt-anthropic-0540`

Snippet: `samples/flt-anthropic/flt-anthropic-0540.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq.LNCC.IsCoord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq.lean#L206-L213) — `flt-anthropic-0541`

Snippet: `samples/flt-anthropic/flt-anthropic-0541.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerTangent.inlO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective.lean#L99-L101) — `flt-anthropic-0542`

Snippet: `samples/flt-anthropic/flt-anthropic-0542.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.BassSerreCusp.X`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.lean#L242-L242) — `flt-anthropic-0543`

Snippet: `samples/flt-anthropic/flt-anthropic-0543.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_pureTensorTerm_dual_and_hybrid_of_depth_twisted_torusFinite_central_growth_of_principalLevel_of_gammaHyp.KcRsCellTermsTw3.w₀At`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_pureTensorTerm_dual_and_hybrid_of_depth_twisted_torusFinite_central_growth_of_principalLevel_of_gammaHyp.lean#L112-L112) — `flt-anthropic-0544`

Snippet: `samples/flt-anthropic/flt-anthropic-0544.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet.Ws3.StepDictBody.homsIntoSubgroup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet.lean#L446-L468) — `flt-anthropic-0545`

Snippet: `samples/flt-anthropic/flt-anthropic-0545.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt.R4GC.downMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt.lean#L1135-L1135) — `flt-anthropic-0546`

Snippet: `samples/flt-anthropic/flt-anthropic-0546.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.PDivINJK.ι`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.lean#L32-L33) — `flt-anthropic-0547`

Snippet: `samples/flt-anthropic/flt-anthropic-0547.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.TOLD0b.scal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean#L297-L297) — `flt-anthropic-0548`

Snippet: `samples/flt-anthropic/flt-anthropic-0548.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd.FrobeniusKernelIdeal.frobPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd.lean#L590-L615) — `flt-anthropic-0549`

Snippet: `samples/flt-anthropic/flt-anthropic-0549.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff.P4mg.mroot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff.lean#L114-L115) — `flt-anthropic-0550`

Snippet: `samples/flt-anthropic/flt-anthropic-0550.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top.JacquetPS2.diff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top.lean#L383-L385) — `flt-anthropic-0551`

Snippet: `samples/flt-anthropic/flt-anthropic-0551.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion.NumberField.WeakApprox.absFamily`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion.lean#L17-L19) — `flt-anthropic-0552`

Snippet: `samples/flt-anthropic/flt-anthropic-0552.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker.W1xLA.ΦHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker.lean#L1038-L1049) — `flt-anthropic-0553`

Snippet: `samples/flt-anthropic/flt-anthropic-0553.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1.ChartMemAsm.deltaPow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1.lean#L297-L298) — `flt-anthropic-0554`

Snippet: `samples/flt-anthropic/flt-anthropic-0554.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton.PrincTriv.mulSection`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton.lean#L36-L37) — `flt-anthropic-0555`

Snippet: `samples/flt-anthropic/flt-anthropic-0555.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_eq_four_mul_add_two_mul_vdet_of_centralizer_apply_eq_zpow_smul_of_isSpecial.DHPhi.Etr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_eq_four_mul_add_two_mul_vdet_of_centralizer_apply_eq_zpow_smul_of_isSpecial.lean#L93-L93) — `flt-anthropic-0556`

Snippet: `samples/flt-anthropic/flt-anthropic-0556.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum.C5Body.AffSES.transferLeft`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum.lean#L19-L35) — `flt-anthropic-0557`

Snippet: `samples/flt-anthropic/flt-anthropic-0557.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.fstA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.lean#L131-L131) — `flt-anthropic-0558`

Snippet: `samples/flt-anthropic/flt-anthropic-0558.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily.U5FreeSubSol.actP`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily.lean#L173-L197) — `flt-anthropic-0559`

Snippet: `samples/flt-anthropic/flt-anthropic-0559.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23Tw.TwCubic`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.lean#L626-L645) — `flt-anthropic-0560`

Snippet: `samples/flt-anthropic/flt-anthropic-0560.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre.P2mDomExt536.mulFst`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre.lean#L198-L200) — `flt-anthropic-0561`

Snippet: `samples/flt-anthropic/flt-anthropic-0561.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets.K7RA5.G`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets.lean#L21-L21) — `flt-anthropic-0562`

Snippet: `samples/flt-anthropic/flt-anthropic-0562.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le.R4TwistNormExist.logAll`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le.lean#L131-L134) — `flt-anthropic-0563`

Snippet: `samples/flt-anthropic/flt-anthropic-0563.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite.P2mFamFG.uprod`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite.lean#L185-L187) — `flt-anthropic-0564`

Snippet: `samples/flt-anthropic/flt-anthropic-0564.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType.FpqcLocalLiftGen.Rch`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType.lean#L60-L60) — `flt-anthropic-0565`

Snippet: `samples/flt-anthropic/flt-anthropic-0565.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10.Q₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.lean#L123-L124) — `flt-anthropic-0566`

Snippet: `samples/flt-anthropic/flt-anthropic-0566.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NumberField.AdelicTrace.traceInt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NumberField_IntegralAdelicTrace.lean#L345-L360) — `flt-anthropic-0567`

Snippet: `samples/flt-anthropic/flt-anthropic-0567.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.LevelP.borelData`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_KatzLevelPClassifyingMaps.lean#L511-L511) — `flt-anthropic-0568`

Snippet: `samples/flt-anthropic/flt-anthropic-0568.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2.HChart.entries`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2.lean#L59-L61) — `flt-anthropic-0569`

Snippet: `samples/flt-anthropic/flt-anthropic-0569.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent.ModularCurve.S3bEmbFrac.Rescales`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent.lean#L138-L141) — `flt-anthropic-0570`

Snippet: `samples/flt-anthropic/flt-anthropic-0570.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.MeroRealize.SL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean#L158-L158) — `flt-anthropic-0571`

Snippet: `samples/flt-anthropic/flt-anthropic-0571.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet.Nat.placesOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet.lean#L32-L33) — `flt-anthropic-0572`

Snippet: `samples/flt-anthropic/flt-anthropic-0572.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2.mulMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.lean#L304-L307) — `flt-anthropic-0573`

Snippet: `samples/flt-anthropic/flt-anthropic-0573.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm.ModularCurve.PDPairing.SanIDX.upE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_heckeT0_comm.lean#L694-L694) — `flt-anthropic-0574`

Snippet: `samples/flt-anthropic/flt-anthropic-0574.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two.AlgebraicGeometry.Scheme.Modules.SpreadUniq.unUp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two.lean#L52-L56) — `flt-anthropic-0575`

Snippet: `samples/flt-anthropic/flt-anthropic-0575.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul.X1FrickeG.IsDiaG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul.lean#L100-L110) — `flt-anthropic-0576`

Snippet: `samples/flt-anthropic/flt-anthropic-0576.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset.AutomorphicForm.PrescribedComponents.SL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset.lean#L26-L28) — `flt-anthropic-0577`

Snippet: `samples/flt-anthropic/flt-anthropic-0577.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.LinearMap.TwoSidedIdeal.WellFoundedGT.WellFoundedLT.IsLocalRing.Submodule.Pi.Algebra.FrobDictPC.Coeff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean#L2531-L2531) — `flt-anthropic-0578`

Snippet: `samples/flt-anthropic/flt-anthropic-0578.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.SpecialFormal.Rigidified.rigidNum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_CartierQuadruple.lean#L151-L163) — `flt-anthropic-0579`

Snippet: `samples/flt-anthropic/flt-anthropic-0579.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPD22.θst`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.lean#L884-L889) — `flt-anthropic-0580`

Snippet: `samples/flt-anthropic/flt-anthropic-0580.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt.B6`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_EisensteinSeries_ramanujan_system_qExpansion_int.lean#L385-L385) — `flt-anthropic-0581`

Snippet: `samples/flt-anthropic/flt-anthropic-0581.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.G2eAsm.cover`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.lean#L299-L300) — `flt-anthropic-0582`

Snippet: `samples/flt-anthropic/flt-anthropic-0582.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.O`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.lean#L470-L470) — `flt-anthropic-0583`

Snippet: `samples/flt-anthropic/flt-anthropic-0583.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.ModularCurve.NodeLocalized.modularEvalRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.lean#L344-L345) — `flt-anthropic-0584`

Snippet: `samples/flt-anthropic/flt-anthropic-0584.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a.piq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.lean#L170-L173) — `flt-anthropic-0585`

Snippet: `samples/flt-anthropic/flt-anthropic-0585.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.S42LevelHopf.coordSeries`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.lean#L132-L135) — `flt-anthropic-0586`

Snippet: `samples/flt-anthropic/flt-anthropic-0586.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D.g`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.lean#L503-L503) — `flt-anthropic-0587`

Snippet: `samples/flt-anthropic/flt-anthropic-0587.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.Dr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L26-L28) — `flt-anthropic-0588`

Snippet: `samples/flt-anthropic/flt-anthropic-0588.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq.P2mLead.chi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq.lean#L151-L151) — `flt-anthropic-0589`

Snippet: `samples/flt-anthropic/flt-anthropic-0589.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.ALRatFun.Idx`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.lean#L70-L70) — `flt-anthropic-0590`

Snippet: `samples/flt-anthropic/flt-anthropic-0590.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq.CerednikDrinfeld.FormalOmega.AffineDescentAux.Lev`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq.lean#L110-L111) — `flt-anthropic-0591`

Snippet: `samples/flt-anthropic/flt-anthropic-0591.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.KJ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.lean#L702-L704) — `flt-anthropic-0592`

Snippet: `samples/flt-anthropic/flt-anthropic-0592.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul.B3CARRIER.HB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul.lean#L81-L81) — `flt-anthropic-0593`

Snippet: `samples/flt-anthropic/flt-anthropic-0593.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.SepLaurent.toDerivation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.lean#L301-L312) — `flt-anthropic-0594`

Snippet: `samples/flt-anthropic/flt-anthropic-0594.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt.IsQS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_EisensteinSeries_ramanujan_system_qExpansion_int.lean#L35-L36) — `flt-anthropic-0595`

Snippet: `samples/flt-anthropic/flt-anthropic-0595.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`WeierstrassCurve.deuringA₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_LevelThreeModulus.lean#L58-L58) — `flt-anthropic-0596`

Snippet: `samples/flt-anthropic/flt-anthropic-0596.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian.RelativeGroupLaw.kwTensorStruct`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.lean#L392-L396) — `flt-anthropic-0597`

Snippet: `samples/flt-anthropic/flt-anthropic-0597.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AutomorphicForm.TransversalMeasure.saturated`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AutomorphicForm_TransversalMeasure.lean#L89-L91) — `flt-anthropic-0598`

Snippet: `samples/flt-anthropic/flt-anthropic-0598.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two.P2mFujisakiD.RK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two.lean#L121-L121) — `flt-anthropic-0599`

Snippet: `samples/flt-anthropic/flt-anthropic-0599.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_isCurveOver_adjoin_range_eq_top_apply_algEquiv_eq_pow_of_pow_eq_one.DescentAux.S`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_isCurveOver_adjoin_range_eq_top_apply_algEquiv_eq_pow_of_pow_eq_one.lean#L197-L199) — `flt-anthropic-0600`

Snippet: `samples/flt-anthropic/flt-anthropic-0600.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral.Ws23CutEval.finWgen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral.lean#L425-L426) — `flt-anthropic-0601`

Snippet: `samples/flt-anthropic/flt-anthropic-0601.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal.pr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.lean#L162-L162) — `flt-anthropic-0602`

Snippet: `samples/flt-anthropic/flt-anthropic-0602.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2.S5asm.ValSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2.lean#L257-L265) — `flt-anthropic-0603`

Snippet: `samples/flt-anthropic/flt-anthropic-0603.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.NilYonedaHom.comp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.lean#L512-L513) — `flt-anthropic-0604`

Snippet: `samples/flt-anthropic/flt-anthropic-0604.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve.QExpSplitDevissage.torusTheta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.lean#L397-L401) — `flt-anthropic-0605`

Snippet: `samples/flt-anthropic/flt-anthropic-0605.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq.RigidificationA.theta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq.lean#L300-L302) — `flt-anthropic-0606`

Snippet: `samples/flt-anthropic/flt-anthropic-0606.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_MultCovering_coeffMap_frobenius_zeroChart_residue_goodFamilyZero.RAT0.IsContent`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_MultCovering_coeffMap_frobenius_zeroChart_residue_goodFamilyZero.lean#L28-L30) — `flt-anthropic-0607`

Snippet: `samples/flt-anthropic/flt-anthropic-0607.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_localBox_meetOrder_eq_of_forall_finiteAdeleEvalAt_eq_one.CSTowerT21.C4T.locT`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_localBox_meetOrder_eq_of_forall_finiteAdeleEvalAt_eq_one.lean#L866-L871) — `flt-anthropic-0608`

Snippet: `samples/flt-anthropic/flt-anthropic-0608.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve.DivisorTerm.Eg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.lean#L35-L36) — `flt-anthropic-0609`

Snippet: `samples/flt-anthropic/flt-anthropic-0609.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.nsmulHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.lean#L1752-L1755) — `flt-anthropic-0610`

Snippet: `samples/flt-anthropic/flt-anthropic-0610.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve.SpanRealProof.transPrimitive`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.lean#L612-L614) — `flt-anthropic-0611`

Snippet: `samples/flt-anthropic/flt-anthropic-0611.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel_of_level.L1Asm22.KerOps.mulK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel_of_level.lean#L152-L156) — `flt-anthropic-0612`

Snippet: `samples/flt-anthropic/flt-anthropic-0612.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_IsNewform_frobenius_quadratic_mem_of_inertia_sub_mem_eigenPlane_tateModule_jZero_of_not_dvd.ValC2.connSpan`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_IsNewform_frobenius_quadratic_mem_of_inertia_sub_mem_eigenPlane_tateModule_jZero_of_not_dvd.lean#L147-L152) — `flt-anthropic-0613`

Snippet: `samples/flt-anthropic/flt-anthropic-0613.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.InfOffC1Geo.cInf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.lean#L87-L87) — `flt-anthropic-0614`

Snippet: `samples/flt-anthropic/flt-anthropic-0614.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.NodeLocalized.jRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_NodeDescent.lean#L22-L24) — `flt-anthropic-0615`

Snippet: `samples/flt-anthropic/flt-anthropic-0615.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.LawDescends.mP`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.lean#L624-L626) — `flt-anthropic-0616`

Snippet: `samples/flt-anthropic/flt-anthropic-0616.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2.KcFlatFamily.expChar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2.lean#L50-L54) — `flt-anthropic-0617`

Snippet: `samples/flt-anthropic/flt-anthropic-0617.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower.degVForget`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.lean#L1063-L1064) — `flt-anthropic-0618`

Snippet: `samples/flt-anthropic/flt-anthropic-0618.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.NumberField.TateGlobal.unitsOutside`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L66-L77) — `flt-anthropic-0619`

Snippet: `samples/flt-anthropic/flt-anthropic-0619.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.StepLineE72.cls`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.lean#L252-L252) — `flt-anthropic-0620`

Snippet: `samples/flt-anthropic/flt-anthropic-0620.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf.IterCech.Staircase.tupKB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.lean#L110-L111) — `flt-anthropic-0621`

Snippet: `samples/flt-anthropic/flt-anthropic-0621.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Real_poitouKernel_admissible_and_archBound.FLT.Gapsw80T75BourbakiKernelDef.gapsw80_t75_BourbakiStripPositivity`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Real_poitouKernel_admissible_and_archBound.lean#L715-L717) — `flt-anthropic-0622`

Snippet: `samples/flt-anthropic/flt-anthropic-0622.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.CuspSpace.cuspWidth`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_CuspSpace.lean#L343-L343) — `flt-anthropic-0623`

Snippet: `samples/flt-anthropic/flt-anthropic-0623.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel.L2Aux.toResidue`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel.lean#L214-L215) — `flt-anthropic-0624`

Snippet: `samples/flt-anthropic/flt-anthropic-0624.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgHomSpreadDirected.Φ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.lean#L117-L119) — `flt-anthropic-0625`

Snippet: `samples/flt-anthropic/flt-anthropic-0625.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2.P2mUnitWeightK.kv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2.lean#L94-L94) — `flt-anthropic-0626`

Snippet: `samples/flt-anthropic/flt-anthropic-0626.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd.NeronLeg1CuspSections.cuspRetraction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd.lean#L680-L701) — `flt-anthropic-0627`

Snippet: `samples/flt-anthropic/flt-anthropic-0627.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero.P2mX3Beta.V₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero.lean#L327-L338) — `flt-anthropic-0628`

Snippet: `samples/flt-anthropic/flt-anthropic-0628.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular.CuspRegComb.ratPart`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular.lean#L96-L96) — `flt-anthropic-0629`

Snippet: `samples/flt-anthropic/flt-anthropic-0629.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le.Ws23.V2.omega`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le.lean#L70-L72) — `flt-anthropic-0630`

Snippet: `samples/flt-anthropic/flt-anthropic-0630.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg.ProperUnifCore.ι`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg.lean#L21-L21) — `flt-anthropic-0631`

Snippet: `samples/flt-anthropic/flt-anthropic-0631.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne.WsB.C6.Dop`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne.lean#L99-L100) — `flt-anthropic-0632`

Snippet: `samples/flt-anthropic/flt-anthropic-0632.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.GlueDatum.ρFin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L129-L130) — `flt-anthropic-0633`

Snippet: `samples/flt-anthropic/flt-anthropic-0633.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible.L4Box.fwd₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible.lean#L107-L108) — `flt-anthropic-0634`

Snippet: `samples/flt-anthropic/flt-anthropic-0634.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt.ren`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.lean#L227-L227) — `flt-anthropic-0635`

Snippet: `samples/flt-anthropic/flt-anthropic-0635.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.K1aOfFinite.rt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.lean#L599-L599) — `flt-anthropic-0636`

Snippet: `samples/flt-anthropic/flt-anthropic-0636.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`TestFunctionAction.checkHomeomorph`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_RepTheory_SchwartzBruhat_CheckConvolution.lean#L25-L26) — `flt-anthropic-0637`

Snippet: `samples/flt-anthropic/flt-anthropic-0637.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModPForms_exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp.EasyAssembly.fM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModPForms_exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp.lean#L359-L359) — `flt-anthropic-0638`

Snippet: `samples/flt-anthropic/flt-anthropic-0638.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq.P2mKcCartierFaithful.seq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_eq_of_map_eq.lean#L153-L155) — `flt-anthropic-0639`

Snippet: `samples/flt-anthropic/flt-anthropic-0639.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm.IwasawaQuot.wt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.lean#L164-L164) — `flt-anthropic-0640`

Snippet: `samples/flt-anthropic/flt-anthropic-0640.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.MultCovering.jBar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_MultCoveringCharts.lean#L43-L43) — `flt-anthropic-0641`

Snippet: `samples/flt-anthropic/flt-anthropic-0641.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit.AlgebraicGeometry.OModulePresheaf.CechRing.B`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit.lean#L217-L219) — `flt-anthropic-0642`

Snippet: `samples/flt-anthropic/flt-anthropic-0642.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.ALDich.traceRepMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.lean#L212-L214) — `flt-anthropic-0643`

Snippet: `samples/flt-anthropic/flt-anthropic-0643.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow.KTwoPow.trCoeffs`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow.lean#L290-L291) — `flt-anthropic-0644`

Snippet: `samples/flt-anthropic/flt-anthropic-0644.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.RelRepS14.uq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.lean#L149-L184) — `flt-anthropic-0645`

Snippet: `samples/flt-anthropic/flt-anthropic-0645.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three.W1xLA.twist`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three.lean#L758-L761) — `flt-anthropic-0646`

Snippet: `samples/flt-anthropic/flt-anthropic-0646.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.J`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.lean#L145-L147) — `flt-anthropic-0647`

Snippet: `samples/flt-anthropic/flt-anthropic-0647.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.ComponentChart.ofTop`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_SemistableCharts.lean#L171-L172) — `flt-anthropic-0648`

Snippet: `samples/flt-anthropic/flt-anthropic-0648.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`HeckeEis.BinaryForm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_HeckeEis_BinaryFormRep.lean#L25-L26) — `flt-anthropic-0649`

Snippet: `samples/flt-anthropic/flt-anthropic-0649.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable.FLT.PrincipalSeriesGL2Padic.PSCarrier.combo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable.lean#L4354-L4355) — `flt-anthropic-0650`

Snippet: `samples/flt-anthropic/flt-anthropic-0650.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.IsInt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.lean#L94-L94) — `flt-anthropic-0651`

Snippet: `samples/flt-anthropic/flt-anthropic-0651.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.Equiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_QMRigidification.lean#L106-L108) — `flt-anthropic-0652`

Snippet: `samples/flt-anthropic/flt-anthropic-0652.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.MulAlgBody.pr2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean#L36-L38) — `flt-anthropic-0653`

Snippet: `samples/flt-anthropic/flt-anthropic-0653.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch.quotMaxAlgEquivTensorQuotK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.lean#L1179-L1218) — `flt-anthropic-0654`

Snippet: `samples/flt-anthropic/flt-anthropic-0654.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex.P2mIdentityComponent.onePt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex.lean#L564-L565) — `flt-anthropic-0655`

Snippet: `samples/flt-anthropic/flt-anthropic-0655.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_two.R4GC.shp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_two.lean#L1083-L1086) — `flt-anthropic-0656`

Snippet: `samples/flt-anthropic/flt-anthropic-0656.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff.PDivRootR.gε`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff.lean#L800-L801) — `flt-anthropic-0657`

Snippet: `samples/flt-anthropic/flt-anthropic-0657.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspFormClass_isZeroAt_slash_ratCast.ModularForm.S06W2.ratUpperTriangularGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspFormClass_isZeroAt_slash_ratCast.lean#L36-L38) — `flt-anthropic-0658`

Snippet: `samples/flt-anthropic/flt-anthropic-0658.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace.KernelHilb.toN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace.lean#L338-L348) — `flt-anthropic-0659`

Snippet: `samples/flt-anthropic/flt-anthropic-0659.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.WeierstrassCurve.Affine.translationHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean#L3021-L3022) — `flt-anthropic-0660`

Snippet: `samples/flt-anthropic/flt-anthropic-0660.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg.NegWt.pol`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg.lean#L137-L137) — `flt-anthropic-0661`

Snippet: `samples/flt-anthropic/flt-anthropic-0661.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul.AlliAux1HB.Bez.r`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_norm_lt_of_heckeTLin_eq_smul.lean#L84-L86) — `flt-anthropic-0662`

Snippet: `samples/flt-anthropic/flt-anthropic-0662.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam.ModularCurve.EIT.Φ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam.lean#L59-L59) — `flt-anthropic-0663`

Snippet: `samples/flt-anthropic/flt-anthropic-0663.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_RelCartier.lean#L12-L14) — `flt-anthropic-0664`

Snippet: `samples/flt-anthropic/flt-anthropic-0664.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728.ModularCurve.TransGen.pmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728.lean#L37-L39) — `flt-anthropic-0665`

Snippet: `samples/flt-anthropic/flt-anthropic-0665.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne.R1MellinOrthogonality.principalUnits`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne.lean#L45-L46) — `flt-anthropic-0666`

Snippet: `samples/flt-anthropic/flt-anthropic-0666.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq.A9819866d.theta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq.lean#L667-L672) — `flt-anthropic-0667`

Snippet: `samples/flt-anthropic/flt-anthropic-0667.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRModelPackage_exists_dRResolvedModelPackageV4_and_dRResolvedModelCharts.MvPolynomial.AlgebraicGeometry.IsLocalRing.IsRegularLocalRing.AlgebraicGeometry.MvPolynomial.CrossingQuotient.V3Sol.smoothOffEdges`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModelPackage_exists_dRResolvedModelPackageV4_and_dRResolvedModelCharts.lean#L1378-L1378) — `flt-anthropic-0668`

Snippet: `samples/flt-anthropic/flt-anthropic-0668.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_two.ConstAdm.incl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_two.lean#L157-L163) — `flt-anthropic-0669`

Snippet: `samples/flt-anthropic/flt-anthropic-0669.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean#L131-L132) — `flt-anthropic-0670`

Snippet: `samples/flt-anthropic/flt-anthropic-0670.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`V3Asm.R`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_ResolvedModelSite.lean#L277-L278) — `flt-anthropic-0671`

Snippet: `samples/flt-anthropic/flt-anthropic-0671.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace.HwCurve.stabEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace.lean#L134-L144) — `flt-anthropic-0672`

Snippet: `samples/flt-anthropic/flt-anthropic-0672.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`M4aHerbrand.idelesTrivialOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_M4aHerbrand_SIdeleClassGroup.lean#L39-L43) — `flt-anthropic-0673`

Snippet: `samples/flt-anthropic/flt-anthropic-0673.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.A2K1A.ΓtSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.lean#L24-L25) — `flt-anthropic-0674`

Snippet: `samples/flt-anthropic/flt-anthropic-0674.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj.W1GLB.ιB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj.lean#L446-L446) — `flt-anthropic-0675`

Snippet: `samples/flt-anthropic/flt-anthropic-0675.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero.ModularCurve.PeriodMapNonvanishing.weightZeroModularForm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero.lean#L53-L82) — `flt-anthropic-0676`

Snippet: `samples/flt-anthropic/flt-anthropic-0676.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3.Ws23PhiFlat.Gfun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3.lean#L353-L356) — `flt-anthropic-0677`

Snippet: `samples/flt-anthropic/flt-anthropic-0677.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LT.TwistedNorm.SigmaConjClasses.mk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TwistedNormClasses.lean#L718-L719) — `flt-anthropic-0678`

Snippet: `samples/flt-anthropic/flt-anthropic-0678.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime.Nat.placesOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime.lean#L28-L29) — `flt-anthropic-0679`

Snippet: `samples/flt-anthropic/flt-anthropic-0679.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable.R4SignProj.liftGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable.lean#L55-L55) — `flt-anthropic-0680`

Snippet: `samples/flt-anthropic/flt-anthropic-0680.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.Place.kw_ffgc_completionTraceF'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean#L394-L401) — `flt-anthropic-0681`

Snippet: `samples/flt-anthropic/flt-anthropic-0681.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve.RationalHomUnits.affSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_finite_rationalHomSet_units.lean#L617-L620) — `flt-anthropic-0682`

Snippet: `samples/flt-anthropic/flt-anthropic-0682.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Pic0_surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius.P2mSurjLang.homSubgroup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Pic0_surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius.lean#L112-L118) — `flt-anthropic-0683`

Snippet: `samples/flt-anthropic/flt-anthropic-0683.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec.Setup.CS₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.lean#L341-L341) — `flt-anthropic-0684`

Snippet: `samples/flt-anthropic/flt-anthropic-0684.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.P2MKcIgusaGroup.Frame.kk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean#L211-L211) — `flt-anthropic-0685`

Snippet: `samples/flt-anthropic/flt-anthropic-0685.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.DSRed.diagRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.lean#L339-L348) — `flt-anthropic-0686`

Snippet: `samples/flt-anthropic/flt-anthropic-0686.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules.ObjGlue.T`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean#L697-L701) — `flt-anthropic-0687`

Snippet: `samples/flt-anthropic/flt-anthropic-0687.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_isGalois_ord_jqModC_dvd_twelve_of_char_two.P2MKcG12.toAdjoinFix`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isGalois_ord_jqModC_dvd_twelve_of_char_two.lean#L574-L579) — `flt-anthropic-0688`

Snippet: `samples/flt-anthropic/flt-anthropic-0688.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.Fact1.HeckeAnalytic.repGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L217-L222) — `flt-anthropic-0689`

Snippet: `samples/flt-anthropic/flt-anthropic-0689.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_AuxLevel_exists_linearEquiv_baseML_prod_ML.AuxIso.ιm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_AuxLevel_exists_linearEquiv_baseML_prod_ML.lean#L574-L576) — `flt-anthropic-0690`

Snippet: `samples/flt-anthropic/flt-anthropic-0690.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange.GenKerVCAux.hom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_IsCyclicGenKernel_variableChange.lean#L22-L23) — `flt-anthropic-0691`

Snippet: `samples/flt-anthropic/flt-anthropic-0691.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.F4CutWords.archProdIncl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.lean#L94-L97) — `flt-anthropic-0692`

Snippet: `samples/flt-anthropic/flt-anthropic-0692.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.primalWtD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.lean#L726-L726) — `flt-anthropic-0693`

Snippet: `samples/flt-anthropic/flt-anthropic-0693.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent.PI0C1.piEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent.lean#L113-L115) — `flt-anthropic-0694`

Snippet: `samples/flt-anthropic/flt-anthropic-0694.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq.P2mS25F0c.content`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq.lean#L91-L92) — `flt-anthropic-0695`

Snippet: `samples/flt-anthropic/flt-anthropic-0695.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_transcendental_lambdaModC.ModularCurve.TrLambda.IsOneUnit`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_transcendental_lambdaModC.lean#L15-L15) — `flt-anthropic-0696`

Snippet: `samples/flt-anthropic/flt-anthropic-0696.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two.ConvPoints.pointsAb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two.lean#L347-L372) — `flt-anthropic-0697`

Snippet: `samples/flt-anthropic/flt-anthropic-0697.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range.Bridge.Kb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range.lean#L12-L12) — `flt-anthropic-0698`

Snippet: `samples/flt-anthropic/flt-anthropic-0698.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.liftKJ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.lean#L722-L729) — `flt-anthropic-0699`

Snippet: `samples/flt-anthropic/flt-anthropic-0699.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AutomorphicForm.archFlowAt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean#L129-L130) — `flt-anthropic-0700`

Snippet: `samples/flt-anthropic/flt-anthropic-0700.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd.W1xLBCH.P`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd.lean#L414-L418) — `flt-anthropic-0701`

Snippet: `samples/flt-anthropic/flt-anthropic-0701.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA.res1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.lean#L673-L675) — `flt-anthropic-0702`

Snippet: `samples/flt-anthropic/flt-anthropic-0702.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.ALRatFun.evφ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.lean#L769-L773) — `flt-anthropic-0703`

Snippet: `samples/flt-anthropic/flt-anthropic-0703.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModPForms_finiteDimensional_modPMod.RedRank.coeffL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModPForms_finiteDimensional_modPMod.lean#L39-L42) — `flt-anthropic-0704`

Snippet: `samples/flt-anthropic/flt-anthropic-0704.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j_of_eq_three_of_dvd.SSN.LR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j_of_eq_three_of_dvd.lean#L87-L87) — `flt-anthropic-0705`

Snippet: `samples/flt-anthropic/flt-anthropic-0705.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GL.slPart`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.lean#L968-L972) — `flt-anthropic-0706`

Snippet: `samples/flt-anthropic/flt-anthropic-0706.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul.RFCompatE165.iota`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul.lean#L90-L92) — `flt-anthropic-0707`

Snippet: `samples/flt-anthropic/flt-anthropic-0707.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_ne_zero.P2MKcA.FC0.EB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_ne_zero.lean#L184-L184) — `flt-anthropic-0708`

Snippet: `samples/flt-anthropic/flt-anthropic-0708.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3.W4DOM.Mmaj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3.lean#L352-L354) — `flt-anthropic-0709`

Snippet: `samples/flt-anthropic/flt-anthropic-0709.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.XHCuspChart.liftI`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.lean#L705-L706) — `flt-anthropic-0710`

Snippet: `samples/flt-anthropic/flt-anthropic-0710.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.JZeroTorsionFinite`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_JZeroTorsionFinite.lean#L13-L14) — `flt-anthropic-0711`

Snippet: `samples/flt-anthropic/flt-anthropic-0711.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials.W2Red.gens`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials.lean#L90-L94) — `flt-anthropic-0712`

Snippet: `samples/flt-anthropic/flt-anthropic-0712.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.OrbifoldSL2.θ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.lean#L181-L185) — `flt-anthropic-0713`

Snippet: `samples/flt-anthropic/flt-anthropic-0713.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Deformation.HondaSystem.Examples.mult`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Dieudonne_FontaineFunctor.lean#L595-L603) — `flt-anthropic-0714`

Snippet: `samples/flt-anthropic/flt-anthropic-0714.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.M4aP3C.CplxIwasawa.botQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean#L25-L25) — `flt-anthropic-0715`

Snippet: `samples/flt-anthropic/flt-anthropic-0715.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime.C4T.locT`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime.lean#L447-L452) — `flt-anthropic-0716`

Snippet: `samples/flt-anthropic/flt-anthropic-0716.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Xif`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.lean#L218-L219) — `flt-anthropic-0717`

Snippet: `samples/flt-anthropic/flt-anthropic-0717.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper.SolFFSuccSepUnit.Rr.val`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper.lean#L45-L45) — `flt-anthropic-0718`

Snippet: `samples/flt-anthropic/flt-anthropic-0718.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous.AvgOp.avg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous.lean#L61-L64) — `flt-anthropic-0719`

Snippet: `samples/flt-anthropic/flt-anthropic-0719.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`PadicAlgCl.ringOfIntegers`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_PadicAlgCl_RingOfIntegers.lean#L11-L12) — `flt-anthropic-0720`

Snippet: `samples/flt-anthropic/flt-anthropic-0720.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq.HasseLiftOrthE96.H`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq.lean#L278-L278) — `flt-anthropic-0721`

Snippet: `samples/flt-anthropic/flt-anthropic-0721.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID.ordU`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.lean#L5073-L5073) — `flt-anthropic-0722`

Snippet: `samples/flt-anthropic/flt-anthropic-0722.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.NewformBadPrimeCoeff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CuspForm_Newforms.lean#L40-L45) — `flt-anthropic-0723`

Snippet: `samples/flt-anthropic/flt-anthropic-0723.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.Deformation.FontaineExtStab.red`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.lean#L82-L84) — `flt-anthropic-0724`

Snippet: `samples/flt-anthropic/flt-anthropic-0724.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.R1AF8D2b.jmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.lean#L743-L743) — `flt-anthropic-0725`

Snippet: `samples/flt-anthropic/flt-anthropic-0725.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR.ThetaKSketch.dualIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR.lean#L24-L26) — `flt-anthropic-0726`

Snippet: `samples/flt-anthropic/flt-anthropic-0726.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq.OSUniqAux.awayCongr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq.lean#L27-L28) — `flt-anthropic-0727`

Snippet: `samples/flt-anthropic/flt-anthropic-0727.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.XHLDMain.AA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean#L647-L647) — `flt-anthropic-0728`

Snippet: `samples/flt-anthropic/flt-anthropic-0728.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair.PDivAlphaZero.pt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair.lean#L446-L447) — `flt-anthropic-0729`

Snippet: `samples/flt-anthropic/flt-anthropic-0729.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq.ANb.qexpHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq.lean#L47-L59) — `flt-anthropic-0730`

Snippet: `samples/flt-anthropic/flt-anthropic-0730.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg.CuspCountX0NBar.labels`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg.lean#L115-L119) — `flt-anthropic-0731`

Snippet: `samples/flt-anthropic/flt-anthropic-0731.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.LanglandsTunnell.CubicInduction.ArchConvCalculus.omega3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.lean#L335-L336) — `flt-anthropic-0732`

Snippet: `samples/flt-anthropic/flt-anthropic-0732.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData.sqUnitSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.lean#L1044-L1044) — `flt-anthropic-0733`

Snippet: `samples/flt-anthropic/flt-anthropic-0733.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.A2LevelOneCrit.B`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.lean#L27-L28) — `flt-anthropic-0734`

Snippet: `samples/flt-anthropic/flt-anthropic-0734.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ProjSpaceCech.GradedModule.Presentation.ker`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean#L719-L721) — `flt-anthropic-0735`

Snippet: `samples/flt-anthropic/flt-anthropic-0735.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.AlgebraicGeometry.OModulePresheaf.Leray.RelHZero.relHZeroHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean#L200-L212) — `flt-anthropic-0736`

Snippet: `samples/flt-anthropic/flt-anthropic-0736.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA.ΦRingEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean#L977-L981) — `flt-anthropic-0737`

Snippet: `samples/flt-anthropic/flt-anthropic-0737.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free.ModelBCAux.bcInv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free.lean#L50-L51) — `flt-anthropic-0738`

Snippet: `samples/flt-anthropic/flt-anthropic-0738.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.fullCMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.lean#L955-L957) — `flt-anthropic-0739`

Snippet: `samples/flt-anthropic/flt-anthropic-0739.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical.P2mKcCritFibre.piRes`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical.lean#L412-L415) — `flt-anthropic-0740`

Snippet: `samples/flt-anthropic/flt-anthropic-0740.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible.TwoChartCech.GluedLinesModel.A0s`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible.lean#L312-L313) — `flt-anthropic-0741`

Snippet: `samples/flt-anthropic/flt-anthropic-0741.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd.TwoGluedLinesBCAux.PSnd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd.lean#L438-L440) — `flt-anthropic-0742`

Snippet: `samples/flt-anthropic/flt-anthropic-0742.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`IsDedekindDomain.selmerGroup.radClass`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_IsDedekindDomain_SelmerConnectingHom.lean#L96-L96) — `flt-anthropic-0743`

Snippet: `samples/flt-anthropic/flt-anthropic-0743.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_hasSum_sharpUnitSeries_qParam.ModularCurve.EIT.divNat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_hasSum_sharpUnitSeries_qParam.lean#L365-L368) — `flt-anthropic-0744`

Snippet: `samples/flt-anthropic/flt-anthropic-0744.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB.pushAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.lean#L144-L146) — `flt-anthropic-0745`

Snippet: `samples/flt-anthropic/flt-anthropic-0745.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self.P2mCliff.Γ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self.lean#L16-L16) — `flt-anthropic-0746`

Snippet: `samples/flt-anthropic/flt-anthropic-0746.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.Ws23PhiFlatM.eM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.lean#L244-L246) — `flt-anthropic-0747`

Snippet: `samples/flt-anthropic/flt-anthropic-0747.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero.P2mWs18V56.Good`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero.lean#L216-L222) — `flt-anthropic-0748`

Snippet: `samples/flt-anthropic/flt-anthropic-0748.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem.dT`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IncidenceSystem_Data_isUnit_det_jacobian_iff.lean#L19-L20) — `flt-anthropic-0749`

Snippet: `samples/flt-anthropic/flt-anthropic-0749.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq.ModularCurve.OmegaS2Iso.e0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq.lean#L476-L476) — `flt-anthropic-0750`

Snippet: `samples/flt-anthropic/flt-anthropic-0750.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.P2mTwistedCompactT.Xi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean#L294-L297) — `flt-anthropic-0751`

Snippet: `samples/flt-anthropic/flt-anthropic-0751.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt.B23K5.toCM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt.lean#L547-L554) — `flt-anthropic-0752`

Snippet: `samples/flt-anthropic/flt-anthropic-0752.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_heckeT_diamondRaw_comm.IharaSolComm.alpha`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean#L332-L342) — `flt-anthropic-0753`

Snippet: `samples/flt-anthropic/flt-anthropic-0753.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.P2mSeesawLocalRep.isoUnitAway`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.lean#L283-L286) — `flt-anthropic-0754`

Snippet: `samples/flt-anthropic/flt-anthropic-0754.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_tateAgreement_v2.ModularCurve.KwF4gRRTate.KwF4gRRTateCohenTateAgreement`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_tateAgreement_v2.lean#L2972-L2981) — `flt-anthropic-0755`

Snippet: `samples/flt-anthropic/flt-anthropic-0755.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.AlgebraicCurve.Submodule.nestedComapMapMkQEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean#L362-L390) — `flt-anthropic-0756`

Snippet: `samples/flt-anthropic/flt-anthropic-0756.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.ConstPullback.homothety`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.lean#L159-L169) — `flt-anthropic-0757`

Snippet: `samples/flt-anthropic/flt-anthropic-0757.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_retraction_binaryFormEval.HeckeEis.retraction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_retraction_binaryFormEval.lean#L342-L343) — `flt-anthropic-0758`

Snippet: `samples/flt-anthropic/flt-anthropic-0758.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`V3Glue.LevelSite.Node`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_ResolvedModelSiteLevel.lean#L42-L42) — `flt-anthropic-0759`

Snippet: `samples/flt-anthropic/flt-anthropic-0759.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure.FreeCoresSol.total`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure.lean#L118-L118) — `flt-anthropic-0760`

Snippet: `samples/flt-anthropic/flt-anthropic-0760.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.idealOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.lean#L239-L240) — `flt-anthropic-0761`

Snippet: `samples/flt-anthropic/flt-anthropic-0761.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField.E160A3.sliceAlgHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField.lean#L216-L226) — `flt-anthropic-0762`

Snippet: `samples/flt-anthropic/flt-anthropic-0762.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.ProperCurveExtension.extend`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.lean#L47-L49) — `flt-anthropic-0763`

Snippet: `samples/flt-anthropic/flt-anthropic-0763.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.NumberField.AdelicFourier.Poisson2Box.boxEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi.lean#L240-L254) — `flt-anthropic-0764`

Snippet: `samples/flt-anthropic/flt-anthropic-0764.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm.AdelicGL2HaarFactor.SProd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.lean#L33-L33) — `flt-anthropic-0765`

Snippet: `samples/flt-anthropic/flt-anthropic-0765.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles.A2BES.mulN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles.lean#L315-L318) — `flt-anthropic-0766`

Snippet: `samples/flt-anthropic/flt-anthropic-0766.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem.Q1Classify13.orb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem.lean#L42-L46) — `flt-anthropic-0767`

Snippet: `samples/flt-anthropic/flt-anthropic-0767.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.CerednikDrinfeld.QM.FakeEllipticCurve.EndIsoExport.cj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.lean#L38-L54) — `flt-anthropic-0768`

Snippet: `samples/flt-anthropic/flt-anthropic-0768.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform.P2mHCLimR.chart`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform.lean#L332-L332) — `flt-anthropic-0769`

Snippet: `samples/flt-anthropic/flt-anthropic-0769.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain.QuotientFlagProof.pfam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain.lean#L670-L670) — `flt-anthropic-0770`

Snippet: `samples/flt-anthropic/flt-anthropic-0770.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.R4Joint.gaussSchwartz`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.lean#L143-L148) — `flt-anthropic-0771`

Snippet: `samples/flt-anthropic/flt-anthropic-0771.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt.UnramTwist.idl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt.lean#L40-L42) — `flt-anthropic-0772`

Snippet: `samples/flt-anthropic/flt-anthropic-0772.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.LBA.Hκ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.lean#L137-L137) — `flt-anthropic-0773`

Snippet: `samples/flt-anthropic/flt-anthropic-0773.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase.W1xLA.ιC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase.lean#L602-L602) — `flt-anthropic-0774`

Snippet: `samples/flt-anthropic/flt-anthropic-0774.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2.LanglandsTunnell.RankinSelberg.GodementAssembly.normSec`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2.lean#L247-L250) — `flt-anthropic-0775`

Snippet: `samples/flt-anthropic/flt-anthropic-0775.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.TwoChartCech.GluedLinesChi.Amb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.lean#L415-L415) — `flt-anthropic-0776`

Snippet: `samples/flt-anthropic/flt-anthropic-0776.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint.TweakGlue.extHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint.lean#L108-L115) — `flt-anthropic-0777`

Snippet: `samples/flt-anthropic/flt-anthropic-0777.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U.ModularCurve.SymmetricTwoVars.newtonAssembled`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U.lean#L424-L425) — `flt-anthropic-0778`

Snippet: `samples/flt-anthropic/flt-anthropic-0778.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.IgusaCover.IsKummerGenerator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_IgusaFunctionField.lean#L39-L43) — `flt-anthropic-0779`

Snippet: `samples/flt-anthropic/flt-anthropic-0779.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn.Ws23.CuspAvg.partE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn.lean#L131-L132) — `flt-anthropic-0780`

Snippet: `samples/flt-anthropic/flt-anthropic-0780.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_levelAut_smul_mem_igusaDisc_of_forall_not_inTube_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.LevelAuts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_levelAut_smul_mem_igusaDisc_of_forall_not_inTube_of_eq_three_of_dvd.lean#L222-L225) — `flt-anthropic-0781`

Snippet: `samples/flt-anthropic/flt-anthropic-0781.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem.ProperUnifBridge.ρi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem.lean#L234-L234) — `flt-anthropic-0782`

Snippet: `samples/flt-anthropic/flt-anthropic-0782.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker.FGH1.dnMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker.lean#L28-L28) — `flt-anthropic-0783`

Snippet: `samples/flt-anthropic/flt-anthropic-0783.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke.FrSpecLawsB.ΓGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke.lean#L28-L29) — `flt-anthropic-0784`

Snippet: `samples/flt-anthropic/flt-anthropic-0784.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero.Ws31.ArchC.Bc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero.lean#L23-L23) — `flt-anthropic-0785`

Snippet: `samples/flt-anthropic/flt-anthropic-0785.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural.P2mTJ2.E01`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural.lean#L183-L185) — `flt-anthropic-0786`

Snippet: `samples/flt-anthropic/flt-anthropic-0786.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real.P2mGramBox.ridE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real.lean#L26-L28) — `flt-anthropic-0787`

Snippet: `samples/flt-anthropic/flt-anthropic-0787.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2.transl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.lean#L80-L81) — `flt-anthropic-0788`

Snippet: `samples/flt-anthropic/flt-anthropic-0788.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH.ModularCurve.ComplexPlaceDictionaryOf.ThirdKindAssemblyH.Inv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH.lean#L29-L29) — `flt-anthropic-0789`

Snippet: `samples/flt-anthropic/flt-anthropic-0789.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker.FFH1.Dr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker.lean#L36-L36) — `flt-anthropic-0790`

Snippet: `samples/flt-anthropic/flt-anthropic-0790.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.PPn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.lean#L39-L39) — `flt-anthropic-0791`

Snippet: `samples/flt-anthropic/flt-anthropic-0791.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ProjSpaceCech.GradedModule.H`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean#L399-L404) — `flt-anthropic-0792`

Snippet: `samples/flt-anthropic/flt-anthropic-0792.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain.R1L2Trunc.sphSum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain.lean#L273-L276) — `flt-anthropic-0793`

Snippet: `samples/flt-anthropic/flt-anthropic-0793.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation.PV1TL.uASm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation.lean#L190-L193) — `flt-anthropic-0794`

Snippet: `samples/flt-anthropic/flt-anthropic-0794.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.LAV.eSlot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.lean#L130-L136) — `flt-anthropic-0795`

Snippet: `samples/flt-anthropic/flt-anthropic-0795.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow.ModularCurve.EtaQSeries.p`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_hasSum_coeff_etaProd_pow.lean#L89-L89) — `flt-anthropic-0796`

Snippet: `samples/flt-anthropic/flt-anthropic-0796.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq.ExtCitation.LocalLevel.Ws25UU.autOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq.lean#L30-L33) — `flt-anthropic-0797`

Snippet: `samples/flt-anthropic/flt-anthropic-0797.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth.WITNESS.awayPart`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth.lean#L199-L199) — `flt-anthropic-0798`

Snippet: `samples/flt-anthropic/flt-anthropic-0798.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two.P2MMultOR.decRingEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two.lean#L240-L246) — `flt-anthropic-0799`

Snippet: `samples/flt-anthropic/flt-anthropic-0799.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar.FltWs29.T27.JN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar.lean#L62-L64) — `flt-anthropic-0800`

Snippet: `samples/flt-anthropic/flt-anthropic-0800.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`FppfRepresentableGroupSchemeSheaf.yonedaCommGrpObjOverRepresentableBy`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FppfGmRepresentable.lean#L180-L183) — `flt-anthropic-0801`

Snippet: `samples/flt-anthropic/flt-anthropic-0801.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CohCarrier.frickeMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CohCarrier_Fricke.lean#L14-L22) — `flt-anthropic-0802`

Snippet: `samples/flt-anthropic/flt-anthropic-0802.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.QuaternionAlgebra.SNEmbedProof.qK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.lean#L21-L21) — `flt-anthropic-0803`

Snippet: `samples/flt-anthropic/flt-anthropic-0803.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.KwF4gRRTate.lmulK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L286-L287) — `flt-anthropic-0804`

Snippet: `samples/flt-anthropic/flt-anthropic-0804.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_functionFieldMapAlongGeneral`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3633-L3637) — `flt-anthropic-0805`

Snippet: `samples/flt-anthropic/flt-anthropic-0805.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED.bcPair`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.lean#L74-L80) — `flt-anthropic-0806`

Snippet: `samples/flt-anthropic/flt-anthropic-0806.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.MZG.Cocycle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.lean#L148-L165) — `flt-anthropic-0807`

Snippet: `samples/flt-anthropic/flt-anthropic-0807.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TateCurve_diffHyp_unconditional.TateCurve.TateCurve.fgCoeff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_diffHyp_unconditional.lean#L1019-L1019) — `flt-anthropic-0808`

Snippet: `samples/flt-anthropic/flt-anthropic-0808.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31.FinUnit.T`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.lean#L136-L139) — `flt-anthropic-0809`

Snippet: `samples/flt-anthropic/flt-anthropic-0809.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD.incl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.lean#L150-L152) — `flt-anthropic-0810`

Snippet: `samples/flt-anthropic/flt-anthropic-0810.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.WeierstrassCurve.Affine.placeOfPointEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean#L779-L781) — `flt-anthropic-0811`

Snippet: `samples/flt-anthropic/flt-anthropic-0811.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE.ptO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.lean#L1709-L1710) — `flt-anthropic-0812`

Snippet: `samples/flt-anthropic/flt-anthropic-0812.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split.A9`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.lean#L2680-L2680) — `flt-anthropic-0813`

Snippet: `samples/flt-anthropic/flt-anthropic-0813.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.AlgebraicCurve.AlgebraicCurve.lSpaceShiftEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.lean#L302-L334) — `flt-anthropic-0814`

Snippet: `samples/flt-anthropic/flt-anthropic-0814.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom.WeierstrassProjModel.ProjBaseChange.zCofactor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom.lean#L100-L102) — `flt-anthropic-0815`

Snippet: `samples/flt-anthropic/flt-anthropic-0815.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions.LocalGL2.bigCellWitness`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions.lean#L156-L163) — `flt-anthropic-0816`

Snippet: `samples/flt-anthropic/flt-anthropic-0816.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule.VInvAsm.rε`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule.lean#L127-L129) — `flt-anthropic-0817`

Snippet: `samples/flt-anthropic/flt-anthropic-0817.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_IsNewform_heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero.HeckeUEigenspaceTate.D'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_IsNewform_heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero.lean#L587-L590) — `flt-anthropic-0818`

Snippet: `samples/flt-anthropic/flt-anthropic-0818.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.TwoChartIntegralModel.chartInfOpen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_TwoChartIntegralModel.lean#L288-L288) — `flt-anthropic-0819`

Snippet: `samples/flt-anthropic/flt-anthropic-0819.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.SymmetricPower.permSMulCommClassMvPowerSeries`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_SymmetricPowerPowerSeriesFTSym.lean#L36-L43) — `flt-anthropic-0820`

Snippet: `samples/flt-anthropic/flt-anthropic-0820.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness.CrossingCount.quotientSpanProdXSubCEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness.lean#L95-L106) — `flt-anthropic-0821`

Snippet: `samples/flt-anthropic/flt-anthropic-0821.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2.LTJacquetFunctional.T`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2.lean#L62-L63) — `flt-anthropic-0822`

Snippet: `samples/flt-anthropic/flt-anthropic-0822.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res.P2mS26IR.P`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_inf_injective_and_exact_of_isZero_res.lean#L447-L449) — `flt-anthropic-0823`

Snippet: `samples/flt-anthropic/flt-anthropic-0823.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two.P2mCentralCovolQuat.δA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two.lean#L492-L494) — `flt-anthropic-0824`

Snippet: `samples/flt-anthropic/flt-anthropic-0824.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations.Fold0Aux.IsOrthArch`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations.lean#L1218-L1219) — `flt-anthropic-0825`

Snippet: `samples/flt-anthropic/flt-anthropic-0825.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type.CerednikDrinfeld.MvFormalGroup.C1Kit.B3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type.lean#L344-L344) — `flt-anthropic-0826`

Snippet: `samples/flt-anthropic/flt-anthropic-0826.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_index_heckeUpper.ModularCurve.IndexHeckeUpper.bezoutRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_index_heckeUpper.lean#L231-L238) — `flt-anthropic-0827`

Snippet: `samples/flt-anthropic/flt-anthropic-0827.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd.DeuringMaxP.Poly.hom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd.lean#L197-L198) — `flt-anthropic-0828`

Snippet: `samples/flt-anthropic/flt-anthropic-0828.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.AlgebraicGeometry.Scheme.TwoAffineOpenCover.UnitComparison.toFunH0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.lean#L35-L39) — `flt-anthropic-0829`

Snippet: `samples/flt-anthropic/flt-anthropic-0829.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.ES1Sol.qC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_pic0Congr_jOne_jH_bot_compat.lean#L243-L243) — `flt-anthropic-0830`

Snippet: `samples/flt-anthropic/flt-anthropic-0830.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.lean#L1295-L1305) — `flt-anthropic-0831`

Snippet: `samples/flt-anthropic/flt-anthropic-0831.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.AlgebraicGeometry.Scheme.Modules.piPowι`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.lean#L132-L149) — `flt-anthropic-0832`

Snippet: `samples/flt-anthropic/flt-anthropic-0832.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient.CHRAux.cocoord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient.lean#L125-L127) — `flt-anthropic-0833`

Snippet: `samples/flt-anthropic/flt-anthropic-0833.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.fwd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.lean#L23-L25) — `flt-anthropic-0834`

Snippet: `samples/flt-anthropic/flt-anthropic-0834.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.CurveModel.σ₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean#L1543-L1543) — `flt-anthropic-0835`

Snippet: `samples/flt-anthropic/flt-anthropic-0835.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.weyl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.lean#L1914-L1914) — `flt-anthropic-0836`

Snippet: `samples/flt-anthropic/flt-anthropic-0836.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq.M4aLocalCFT.intSwapPair`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_sUnitQuot_fixedRank_eq.lean#L2430-L2457) — `flt-anthropic-0837`

Snippet: `samples/flt-anthropic/flt-anthropic-0837.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit.GoodReductionJacobian.RelativeGroupLaw.kwUniversalMul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit.lean#L405-L407) — `flt-anthropic-0838`

Snippet: `samples/flt-anthropic/flt-anthropic-0838.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level.AUXProof.rHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level.lean#L181-L196) — `flt-anthropic-0839`

Snippet: `samples/flt-anthropic/flt-anthropic-0839.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.M4aP3C.CplxSmooth.conjCLM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean#L992-L992) — `flt-anthropic-0840`

Snippet: `samples/flt-anthropic/flt-anthropic-0840.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.P2mGrp.tracePairing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.lean#L328-L335) — `flt-anthropic-0841`

Snippet: `samples/flt-anthropic/flt-anthropic-0841.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.SolKS.Dg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.lean#L625-L626) — `flt-anthropic-0842`

Snippet: `samples/flt-anthropic/flt-anthropic-0842.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.cV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L502-L503) — `flt-anthropic-0843`

Snippet: `samples/flt-anthropic/flt-anthropic-0843.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.lean#L49-L49) — `flt-anthropic-0844`

Snippet: `samples/flt-anthropic/flt-anthropic-0844.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections.ExZar.δ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections.lean#L771-L772) — `flt-anthropic-0845`

Snippet: `samples/flt-anthropic/flt-anthropic-0845.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.MultCovering.zeroChart`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_MultCoveringCharts.lean#L86-L88) — `flt-anthropic-0846`

Snippet: `samples/flt-anthropic/flt-anthropic-0846.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_SSLevelDatum_finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice.RibetAssembly69.EngineDatum.gX₀`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SSLevelDatum_finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice.lean#L1382-L1384) — `flt-anthropic-0847`

Snippet: `samples/flt-anthropic/flt-anthropic-0847.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.vtx`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.lean#L244-L244) — `flt-anthropic-0848`

Snippet: `samples/flt-anthropic/flt-anthropic-0848.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.AutomorphicForm.WeylIntegrable.stepElt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean#L1605-L1605) — `flt-anthropic-0849`

Snippet: `samples/flt-anthropic/flt-anthropic-0849.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA.downMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean#L85-L85) — `flt-anthropic-0850`

Snippet: `samples/flt-anthropic/flt-anthropic-0850.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.P2mTwistedCompactT.nrm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean#L111-L111) — `flt-anthropic-0851`

Snippet: `samples/flt-anthropic/flt-anthropic-0851.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.HeckeCharacter.archRealProjTau`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LT_HeckeChar_exists_heckeCharOfRayClassChar.lean#L244-L248) — `flt-anthropic-0852`

Snippet: `samples/flt-anthropic/flt-anthropic-0852.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.P2mTwistedCentralizerModCentre.Xi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean#L294-L297) — `flt-anthropic-0853`

Snippet: `samples/flt-anthropic/flt-anthropic-0853.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.CSTower.isUnitOfEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.lean#L803-L808) — `flt-anthropic-0854`

Snippet: `samples/flt-anthropic/flt-anthropic-0854.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero.CharpS10bB.Model.algFinAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero.lean#L839-L839) — `flt-anthropic-0855`

Snippet: `samples/flt-anthropic/flt-anthropic-0855.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector.F1Asm.awayToOne`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector.lean#L69-L71) — `flt-anthropic-0856`

Snippet: `samples/flt-anthropic/flt-anthropic-0856.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.proj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.lean#L349-L351) — `flt-anthropic-0857`

Snippet: `samples/flt-anthropic/flt-anthropic-0857.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre.AutomorphicForm.stdPins`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre.lean#L38-L40) — `flt-anthropic-0858`

Snippet: `samples/flt-anthropic/flt-anthropic-0858.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.Place.ramificationIndexAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_Correspondence.lean#L211-L213) — `flt-anthropic-0859`

Snippet: `samples/flt-anthropic/flt-anthropic-0859.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.P2mKcCommutantLT.sq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.lean#L570-L572) — `flt-anthropic-0860`

Snippet: `samples/flt-anthropic/flt-anthropic-0860.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.DescentAction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_DescentAction.lean#L69-L74) — `flt-anthropic-0861`

Snippet: `samples/flt-anthropic/flt-anthropic-0861.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Pic0_exists_injective_conorm_map_torsion_eq_of_isAlgClosed.I5.torsionMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Pic0_exists_injective_conorm_map_torsion_eq_of_isAlgClosed.lean#L33-L34) — `flt-anthropic-0862`

Snippet: `samples/flt-anthropic/flt-anthropic-0862.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf.HilbComparisonAssembly.sheafOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf.lean#L35-L37) — `flt-anthropic-0863`

Snippet: `samples/flt-anthropic/flt-anthropic-0863.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a.gl2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.lean#L177-L178) — `flt-anthropic-0864`

Snippet: `samples/flt-anthropic/flt-anthropic-0864.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue.LocalComparison.ellT`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.lean#L706-L711) — `flt-anthropic-0865`

Snippet: `samples/flt-anthropic/flt-anthropic-0865.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq.TraceClosedBody.mkS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq.lean#L245-L246) — `flt-anthropic-0866`

Snippet: `samples/flt-anthropic/flt-anthropic-0866.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.R4Joint.coordInv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.lean#L174-L175) — `flt-anthropic-0867`

Snippet: `samples/flt-anthropic/flt-anthropic-0867.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.CohCarrier.BoundaryEisH.orbOne`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.lean#L384-L385) — `flt-anthropic-0868`

Snippet: `samples/flt-anthropic/flt-anthropic-0868.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_isLocalBridge2_injective.LB1EX.toIntLinearMapOfModules`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_isLocalBridge2_injective.lean#L422-L427) — `flt-anthropic-0869`

Snippet: `samples/flt-anthropic/flt-anthropic-0869.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.R1IwTorus.st`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.lean#L820-L820) — `flt-anthropic-0870`

Snippet: `samples/flt-anthropic/flt-anthropic-0870.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank.EscompRank.pullPar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank.lean#L35-L43) — `flt-anthropic-0871`

Snippet: `samples/flt-anthropic/flt-anthropic-0871.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.P2mKcZp2Matrix.B`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.lean#L100-L100) — `flt-anthropic-0872`

Snippet: `samples/flt-anthropic/flt-anthropic-0872.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve.ETEGlue.locRed`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve.lean#L65-L66) — `flt-anthropic-0873`

Snippet: `samples/flt-anthropic/flt-anthropic-0873.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.SupModelProof.thetaR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.lean#L635-L637) — `flt-anthropic-0874`

Snippet: `samples/flt-anthropic/flt-anthropic-0874.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`FppfCohomologyLES.FppfH`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FppfCohomologyLES.lean#L175-L177) — `flt-anthropic-0875`

Snippet: `samples/flt-anthropic/flt-anthropic-0875.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.ModularCurve.PDPairing.CuspTower.towerLift`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean#L1287-L1288) — `flt-anthropic-0876`

Snippet: `samples/flt-anthropic/flt-anthropic-0876.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.LBA.dκ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.lean#L129-L132) — `flt-anthropic-0877`

Snippet: `samples/flt-anthropic/flt-anthropic-0877.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.AutomorphicForm.WeylIntegrable.eUnit`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean#L991-L991) — `flt-anthropic-0878`

Snippet: `samples/flt-anthropic/flt-anthropic-0878.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.Reduce95.coordsInf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two.lean#L1669-L1669) — `flt-anthropic-0879`

Snippet: `samples/flt-anthropic/flt-anthropic-0879.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`SwdAlgebra.ev`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_SwdAlgebra.lean#L26-L27) — `flt-anthropic-0880`

Snippet: `samples/flt-anthropic/flt-anthropic-0880.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm.HopfAlgebra.OrdBC.inclM`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm.lean#L107-L109) — `flt-anthropic-0881`

Snippet: `samples/flt-anthropic/flt-anthropic-0881.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve.X1OmegaIso.coefZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.lean#L254-L254) — `flt-anthropic-0882`

Snippet: `samples/flt-anthropic/flt-anthropic-0882.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero.PolyAux.normPoly`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero.lean#L72-L73) — `flt-anthropic-0883`

Snippet: `samples/flt-anthropic/flt-anthropic-0883.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_of_projPresentation_monoidalV2.AlgebraicGeometry.P2mSegreGG.DD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_of_projPresentation_monoidalV2.lean#L72-L73) — `flt-anthropic-0884`

Snippet: `samples/flt-anthropic/flt-anthropic-0884.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.ArchPlace.realGammaAt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_ArchPlace.lean#L117-L118) — `flt-anthropic-0885`

Snippet: `samples/flt-anthropic/flt-anthropic-0885.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.P2mKcCommutantLT.ff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.lean#L178-L180) — `flt-anthropic-0886`

Snippet: `samples/flt-anthropic/flt-anthropic-0886.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_linkedScalars_of_eq_three_of_dvd.C3Kit2.fixedEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_linkedScalars_of_eq_three_of_dvd.lean#L208-L215) — `flt-anthropic-0887`

Snippet: `samples/flt-anthropic/flt-anthropic-0887.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure.AutomorphicForm.SemiLocalGL2HaarFactor.kerSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure.lean#L597-L600) — `flt-anthropic-0888`

Snippet: `samples/flt-anthropic/flt-anthropic-0888.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve.PoincareDualIntegrality.gam`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.lean#L95-L95) — `flt-anthropic-0889`

Snippet: `samples/flt-anthropic/flt-anthropic-0889.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.R4GC.downMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean#L1134-L1134) — `flt-anthropic-0890`

Snippet: `samples/flt-anthropic/flt-anthropic-0890.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`LanglandsTunnell.CubicInduction.finEmbedN`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31.lean#L114-L121) — `flt-anthropic-0891`

Snippet: `samples/flt-anthropic/flt-anthropic-0891.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv.NumberField.PlaceDecomp.FCFamily.chosen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv.lean#L187-L189) — `flt-anthropic-0892`

Snippet: `samples/flt-anthropic/flt-anthropic-0892.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType.ImageCurveDet.evalHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType.lean#L202-L203) — `flt-anthropic-0893`

Snippet: `samples/flt-anthropic/flt-anthropic-0893.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor.DetFrob.diagAdic`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor.lean#L214-L229) — `flt-anthropic-0894`

Snippet: `samples/flt-anthropic/flt-anthropic-0894.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ProjSpaceCech.GradedModule.Presentation.kerIncl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean#L723-L727) — `flt-anthropic-0895`

Snippet: `samples/flt-anthropic/flt-anthropic-0895.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField.ModularCurve.ModularCurve.GaussPres.IsPres`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField.lean#L45-L45) — `flt-anthropic-0896`

Snippet: `samples/flt-anthropic/flt-anthropic-0896.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.IntermediateField.NumberField.LevelArith.EQBK.H2ρ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.lean#L635-L647) — `flt-anthropic-0897`

Snippet: `samples/flt-anthropic/flt-anthropic-0897.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two.R3wSol.CommQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two.lean#L217-L218) — `flt-anthropic-0898`

Snippet: `samples/flt-anthropic/flt-anthropic-0898.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finiteBySections_rosatiCompatible_of_isAlgClosed.StarTwist29.tfold`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finiteBySections_rosatiCompatible_of_isAlgClosed.lean#L52-L53) — `flt-anthropic-0899`

Snippet: `samples/flt-anthropic/flt-anthropic-0899.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AutomorphicForm.StandardKernel.entryBox`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AutomorphicForm_SmoothingKernel.lean#L871-L872) — `flt-anthropic-0900`

Snippet: `samples/flt-anthropic/flt-anthropic-0900.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso.ιR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.lean#L156-L156) — `flt-anthropic-0901`

Snippet: `samples/flt-anthropic/flt-anthropic-0901.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq.ιQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.lean#L283-L283) — `flt-anthropic-0902`

Snippet: `samples/flt-anthropic/flt-anthropic-0902.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5.ψmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.lean#L114-L119) — `flt-anthropic-0903`

Snippet: `samples/flt-anthropic/flt-anthropic-0903.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.ModularCurve.GaussQExpRP.gaussRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean#L467-L498) — `flt-anthropic-0904`

Snippet: `samples/flt-anthropic/flt-anthropic-0904.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation.fY`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.lean#L52-L53) — `flt-anthropic-0905`

Snippet: `samples/flt-anthropic/flt-anthropic-0905.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford.NTerm.kerToK0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_exists_mumfordTruncation_of_flat_complex.lean#L117-L122) — `flt-anthropic-0906`

Snippet: `samples/flt-anthropic/flt-anthropic-0906.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.P2mSchlessingerUniversal.Hull.τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.lean#L366-L411) — `flt-anthropic-0907`

Snippet: `samples/flt-anthropic/flt-anthropic-0907.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq.R4W3.Haux`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq.lean#L244-L245) — `flt-anthropic-0908`

Snippet: `samples/flt-anthropic/flt-anthropic-0908.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq.INVARSol.a`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq.lean#L50-L52) — `flt-anthropic-0909`

Snippet: `samples/flt-anthropic/flt-anthropic-0909.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.P2mGExt.Chunk.jD`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean#L577-L579) — `flt-anthropic-0910`

Snippet: `samples/flt-anthropic/flt-anthropic-0910.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.ModularCurve.kw_surgehgf4_hSD_genSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3031-L3034) — `flt-anthropic-0911`

Snippet: `samples/flt-anthropic/flt-anthropic-0911.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW.downMat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.lean#L79-L79) — `flt-anthropic-0912`

Snippet: `samples/flt-anthropic/flt-anthropic-0912.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit.K3cLocMax.LambdaPrime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit.lean#L453-L461) — `flt-anthropic-0913`

Snippet: `samples/flt-anthropic/flt-anthropic-0913.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction.P2mKcLevelTwistAction.G`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction.lean#L104-L104) — `flt-anthropic-0914`

Snippet: `samples/flt-anthropic/flt-anthropic-0914.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi.WsC.S2H.Lap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi.lean#L36-L36) — `flt-anthropic-0915`

Snippet: `samples/flt-anthropic/flt-anthropic-0915.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero.P2MKcA.M1728.cyc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero.lean#L328-L331) — `flt-anthropic-0916`

Snippet: `samples/flt-anthropic/flt-anthropic-0916.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.Place.poleMulUniformizerPow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L393-L400) — `flt-anthropic-0917`

Snippet: `samples/flt-anthropic/flt-anthropic-0917.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.RiemannForm.modulePair`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_ThetaGroup.lean#L155-L155) — `flt-anthropic-0918`

Snippet: `samples/flt-anthropic/flt-anthropic-0918.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank.M4aHerbrand.GaloisTensor.splitEquivOver`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank.lean#L7391-L7397) — `flt-anthropic-0919`

Snippet: `samples/flt-anthropic/flt-anthropic-0919.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.delta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L289-L290) — `flt-anthropic-0920`

Snippet: `samples/flt-anthropic/flt-anthropic-0920.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_pow_smul_mem_span_degeneracy_inertiaAugmentation_of_forall_weilPairing_fricke_eq_zero_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd.TateTransfer.tmap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_pow_smul_mem_span_degeneracy_inertiaAugmentation_of_forall_weilPairing_fricke_eq_zero_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd.lean#L105-L120) — `flt-anthropic-0921`

Snippet: `samples/flt-anthropic/flt-anthropic-0921.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.MvPolynomial.TruncatedBox.K`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.lean#L22-L23) — `flt-anthropic-0922`

Snippet: `samples/flt-anthropic/flt-anthropic-0922.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq.T4bPreimage.swapO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq.lean#L19-L20) — `flt-anthropic-0923`

Snippet: `samples/flt-anthropic/flt-anthropic-0923.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupCovolume.GG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.lean#L282-L282) — `flt-anthropic-0924`

Snippet: `samples/flt-anthropic/flt-anthropic-0924.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PeriodPair_jLattice_surjective.ModularCurve.kwQepw120c_DiscriminantCuspVanishingProp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PeriodPair_jLattice_surjective.lean#L587-L589) — `flt-anthropic-0925`

Snippet: `samples/flt-anthropic/flt-anthropic-0925.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul.P2mLawPresW.PInI`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul.lean#L186-L186) — `flt-anthropic-0926`

Snippet: `samples/flt-anthropic/flt-anthropic-0926.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.IsPar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L2935-L2936) — `flt-anthropic-0927`

Snippet: `samples/flt-anthropic/flt-anthropic-0927.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.DescentAction.repAct`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_DescentAction.lean#L176-L176) — `flt-anthropic-0928`

Snippet: `samples/flt-anthropic/flt-anthropic-0928.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant.AutomorphicForm.TwistedOrbitalEulerU.Gad`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant.lean#L33-L33) — `flt-anthropic-0929`

Snippet: `samples/flt-anthropic/flt-anthropic-0929.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level.R4TateModelK.Γgl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level.lean#L47-L47) — `flt-anthropic-0930`

Snippet: `samples/flt-anthropic/flt-anthropic-0930.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve.Omega2ResidueProof.thetaJInt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.lean#L97-L97) — `flt-anthropic-0931`

Snippet: `samples/flt-anthropic/flt-anthropic-0931.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa.Ws23Arch.iwB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa.lean#L171-L174) — `flt-anthropic-0932`

Snippet: `samples/flt-anthropic/flt-anthropic-0932.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.G2eAsm.q₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.lean#L361-L361) — `flt-anthropic-0933`

Snippet: `samples/flt-anthropic/flt-anthropic-0933.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.P2mTwoTermH0Ann.ι1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.lean#L115-L115) — `flt-anthropic-0934`

Snippet: `samples/flt-anthropic/flt-anthropic-0934.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt.AutomorphicForm.MaassDictionary.rotAt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt.lean#L141-L144) — `flt-anthropic-0935`

Snippet: `samples/flt-anthropic/flt-anthropic-0935.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MC25.linForm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.lean#L1242-L1243) — `flt-anthropic-0936`

Snippet: `samples/flt-anthropic/flt-anthropic-0936.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq.P2mLaw535S.A0'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq.lean#L226-L226) — `flt-anthropic-0937`

Snippet: `samples/flt-anthropic/flt-anthropic-0937.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne.Ws22.DIM.nodeDivisor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne.lean#L150-L150) — `flt-anthropic-0938`

Snippet: `samples/flt-anthropic/flt-anthropic-0938.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local.CerednikDrinfeld.QM.FakeEllipticCurve.CerednikDrinfeld.BodyL2.RepresentsExtraLevel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local.lean#L858-L887) — `flt-anthropic-0939`

Snippet: `samples/flt-anthropic/flt-anthropic-0939.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`IharaLemma.IdempotentSplitting.cornerRingLinearEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_IharaLemma_IdempotentSplitting.lean#L214-L233) — `flt-anthropic-0940`

Snippet: `samples/flt-anthropic/flt-anthropic-0940.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.p`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.lean#L77-L77) — `flt-anthropic-0941`

Snippet: `samples/flt-anthropic/flt-anthropic-0941.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart.B2SubV.Lbar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart.lean#L41-L41) — `flt-anthropic-0942`

Snippet: `samples/flt-anthropic/flt-anthropic-0942.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.KeyLeftSkel.Pab`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.lean#L1087-L1087) — `flt-anthropic-0943`

Snippet: `samples/flt-anthropic/flt-anthropic-0943.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal.wordWalk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L1218-L1220) — `flt-anthropic-0944`

Snippet: `samples/flt-anthropic/flt-anthropic-0944.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.lean#L418-L437) — `flt-anthropic-0945`

Snippet: `samples/flt-anthropic/flt-anthropic-0945.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_multiplicativeTypeNat_inf_ker_reductionModL_eisensteinTorsionBar.KDMUDEngine.ι`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_multiplicativeTypeNat_inf_ker_reductionModL_eisensteinTorsionBar.lean#L99-L100) — `flt-anthropic-0946`

Snippet: `samples/flt-anthropic/flt-anthropic-0946.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_full_eq_adjoin_primes.ModularCurve.W1.cycUnit`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_full_eq_adjoin_primes.lean#L194-L195) — `flt-anthropic-0947`

Snippet: `samples/flt-anthropic/flt-anthropic-0947.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.X1DiamondLift.expandPS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean#L709-L710) — `flt-anthropic-0948`

Snippet: `samples/flt-anthropic/flt-anthropic-0948.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol.wt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_pairing_binaryForm_linePow.lean#L48-L48) — `flt-anthropic-0949`

Snippet: `samples/flt-anthropic/flt-anthropic-0949.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar.ISMain.Obox`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar.lean#L608-L608) — `flt-anthropic-0950`

Snippet: `samples/flt-anthropic/flt-anthropic-0950.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NumberField.StandardAddChar.AdelicTraceData.psiK`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NumberField_StandardGlobalAddChar.lean#L61-L62) — `flt-anthropic-0951`

Snippet: `samples/flt-anthropic/flt-anthropic-0951.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq.Sub2c.twist`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq.lean#L103-L108) — `flt-anthropic-0952`

Snippet: `samples/flt-anthropic/flt-anthropic-0952.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.BassSerreCuspDim.ev`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean#L51-L54) — `flt-anthropic-0953`

Snippet: `samples/flt-anthropic/flt-anthropic-0953.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7.ofR₁`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.lean#L2369-L2369) — `flt-anthropic-0954`

Snippet: `samples/flt-anthropic/flt-anthropic-0954.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerHull.Datum.resR`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.lean#L689-L691) — `flt-anthropic-0955`

Snippet: `samples/flt-anthropic/flt-anthropic-0955.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Module.HopfAlgebra.LocEt.stdOrder`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.lean#L1980-L1980) — `flt-anthropic-0956`

Snippet: `samples/flt-anthropic/flt-anthropic-0956.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T69AdmC2RemintZktSummable.gapsw80_t69_KernelC2Decay`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_archTermDerived_le_log_abs_discr.lean#L3566-L3569) — `flt-anthropic-0957`

Snippet: `samples/flt-anthropic/flt-anthropic-0957.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.AutomorphicForm.TKNHaar.ratCentralHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.lean#L28-L29) — `flt-anthropic-0958`

Snippet: `samples/flt-anthropic/flt-anthropic-0958.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided.K9F2.sig`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided.lean#L160-L162) — `flt-anthropic-0959`

Snippet: `samples/flt-anthropic/flt-anthropic-0959.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal.coordAt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean#L1443-L1443) — `flt-anthropic-0960`

Snippet: `samples/flt-anthropic/flt-anthropic-0960.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean.ArchInvProof.Mc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_groupCohomology_exists_injective_dual_continuousH2_archimedean.lean#L77-L77) — `flt-anthropic-0961`

Snippet: `samples/flt-anthropic/flt-anthropic-0961.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.FrickeCuspTransport.Φ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean#L615-L615) — `flt-anthropic-0962`

Snippet: `samples/flt-anthropic/flt-anthropic-0962.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero.UnramW17.scalarHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero.lean#L74-L74) — `flt-anthropic-0963`

Snippet: `samples/flt-anthropic/flt-anthropic-0963.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.x1FunctionFieldBar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_X1.lean#L182-L184) — `flt-anthropic-0964`

Snippet: `samples/flt-anthropic/flt-anthropic-0964.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ.TWFreeSol.fL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ.lean#L753-L760) — `flt-anthropic-0965`

Snippet: `samples/flt-anthropic/flt-anthropic-0965.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3.KB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.lean#L63-L64) — `flt-anthropic-0966`

Snippet: `samples/flt-anthropic/flt-anthropic-0966.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.Ws1.H2K.Scaffold.E`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.lean#L25-L25) — `flt-anthropic-0967`

Snippet: `samples/flt-anthropic/flt-anthropic-0967.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero.GenFF.iota0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero.lean#L82-L85) — `flt-anthropic-0968`

Snippet: `samples/flt-anthropic/flt-anthropic-0968.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq.InfGroupLawA3.π₂`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq.lean#L367-L368) — `flt-anthropic-0969`

Snippet: `samples/flt-anthropic/flt-anthropic-0969.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.kw_ev_e`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassProjModel_addMorphism_zeroSect_mul.lean#L208-L210) — `flt-anthropic-0970`

Snippet: `samples/flt-anthropic/flt-anthropic-0970.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory.UnitGroupHaar.ν`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.lean#L220-L220) — `flt-anthropic-0971`

Snippet: `samples/flt-anthropic/flt-anthropic-0971.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.DS.transport`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.lean#L871-L874) — `flt-anthropic-0972`

Snippet: `samples/flt-anthropic/flt-anthropic-0972.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre.Vertex`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.lean#L19-L20) — `flt-anthropic-0973`

Snippet: `samples/flt-anthropic/flt-anthropic-0973.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.AlgebraicCurve.ChartPrimitiveTransportProof.germAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.lean#L339-L339) — `flt-anthropic-0974`

Snippet: `samples/flt-anthropic/flt-anthropic-0974.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.P2MMultE.dualBC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.lean#L440-L443) — `flt-anthropic-0975`

Snippet: `samples/flt-anthropic/flt-anthropic-0975.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_hFunctionFieldAction_smul.DrinfeldCurve.GenCount.Ly`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_DrinfeldCurve_natCard_place_restrictAlong_eq_hFunctionFieldAction_smul.lean#L815-L815) — `flt-anthropic-0976`

Snippet: `samples/flt-anthropic/flt-anthropic-0976.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily.vert`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_cellDissection.lean#L144-L144) — `flt-anthropic-0977`

Snippet: `samples/flt-anthropic/flt-anthropic-0977.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.V3AsmMock.ξb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.lean#L763-L763) — `flt-anthropic-0978`

Snippet: `samples/flt-anthropic/flt-anthropic-0978.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.Module.quotSMulTopQuotSMulTopComm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.lean#L746-L750) — `flt-anthropic-0979`

Snippet: `samples/flt-anthropic/flt-anthropic-0979.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex.P2mSplitFibreSmoothComplex.coordsHomeo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex.lean#L183-L186) — `flt-anthropic-0980`

Snippet: `samples/flt-anthropic/flt-anthropic-0980.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt.FibreConnGeometry.τ1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt.lean#L446-L446) — `flt-anthropic-0981`

Snippet: `samples/flt-anthropic/flt-anthropic-0981.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt.NoncommPair.hatQ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt.lean#L109-L110) — `flt-anthropic-0982`

Snippet: `samples/flt-anthropic/flt-anthropic-0982.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible.KirillovSchwartzEngine.cyc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible.lean#L25-L26) — `flt-anthropic-0983`

Snippet: `samples/flt-anthropic/flt-anthropic-0983.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup.TateRankSol.regRep`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup.lean#L23-L35) — `flt-anthropic-0984`

Snippet: `samples/flt-anthropic/flt-anthropic-0984.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one.CutAlg.cotangentEquivOfFormallyEtale`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one.lean#L328-L331) — `flt-anthropic-0985`

Snippet: `samples/flt-anthropic/flt-anthropic-0985.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ArtinL.Abelian.IsUnramifiedAt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ArtinL_Abelian.lean#L33-L34) — `flt-anthropic-0986`

Snippet: `samples/flt-anthropic/flt-anthropic-0986.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.GrassH2.Ctx.u`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.lean#L291-L291) — `flt-anthropic-0987`

Snippet: `samples/flt-anthropic/flt-anthropic-0987.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerHull.fac`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.lean#L402-L402) — `flt-anthropic-0988`

Snippet: `samples/flt-anthropic/flt-anthropic-0988.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.CerednikDrinfeld.QM.SpecialOfFEC.sc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.lean#L111-L111) — `flt-anthropic-0989`

Snippet: `samples/flt-anthropic/flt-anthropic-0989.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.LTJacquetStab.path`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.lean#L410-L410) — `flt-anthropic-0990`

Snippet: `samples/flt-anthropic/flt-anthropic-0990.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux.fstPresheafHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.lean#L123-L128) — `flt-anthropic-0991`

Snippet: `samples/flt-anthropic/flt-anthropic-0991.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms.CohL2.Head.sEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms.lean#L101-L102) — `flt-anthropic-0992`

Snippet: `samples/flt-anthropic/flt-anthropic-0992.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.InjK0.ψ_`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.lean#L52-L52) — `flt-anthropic-0993`

Snippet: `samples/flt-anthropic/flt-anthropic-0993.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.Cells.dualCellIntegrand`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.lean#L2692-L2701) — `flt-anthropic-0994`

Snippet: `samples/flt-anthropic/flt-anthropic-0994.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.UVCrossingModel.nfCoeff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_UVCrossingDominantIndices.lean#L15-L17) — `flt-anthropic-0995`

Snippet: `samples/flt-anthropic/flt-anthropic-0995.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback.FBC.pullbackCompCongr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback.lean#L33-L35) — `flt-anthropic-0996`

Snippet: `samples/flt-anthropic/flt-anthropic-0996.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd.AdelicSlice.s1_Zhat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd.lean#L367-L384) — `flt-anthropic-0997`

Snippet: `samples/flt-anthropic/flt-anthropic-0997.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three.T2Aux.ev`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three.lean#L197-L198) — `flt-anthropic-0998`

Snippet: `samples/flt-anthropic/flt-anthropic-0998.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt.CurveInjSol.shiftPolyZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt.lean#L100-L102) — `flt-anthropic-0999`

Snippet: `samples/flt-anthropic/flt-anthropic-0999.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.


## Formal Frontier (41 flagged)

### [`TopCat.Sheaf.OpenBaseChange.baseChangeIso`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenBaseChange.lean#L163-L204) — `formal-frontier-0031`

Snippet: `samples/formal-frontier/formal-frontier-0031.lean`

- **verdict**: `too_narrow`
- **intended_object**: The open base change isomorphism. For a continuous map f : X → Y and an open V ⊆ Y, it identifies (f_* F)|_V with (f|_{f⁻¹V})_*(F|_{f⁻¹V}), naturally in the sheaf F on X; as functors, i^*_V ∘ f_* ≅ (f_V)_* ∘ i^*_{f⁻¹V}. This comes from the docstring, the module docs and the companion mate lemmas.
- **explanation**: The construction itself is correct. The body:
1. Uses `leftAdjointUniq` to compare Mathlib's `TopCat.Sheaf.pullback` along each open inclusion with the naive pullback `IsOpenEmbedding.sheafPullback`, which is just composition with the image functor on opens.
2. Builds the naive square from `sheafPushforwardContinuousComp`/`Iso` and the equality of opens `preimageOpensIso`.

This gives the standard natural isomorphism (f_*F)|_V ≅ (f_V)_*(F|_{f⁻¹V}).

However, the definition fixes the coefficient category to `Type v`, and no step needs that:
- `leftAdjointUniq`, `sheafPushforwardContinuousComp`/`Iso` and `IsOpenEmbedding.sheafPullback` work for any coefficient category.
- Mathlib's `TopCat.Sheaf.pullback A f` and `pullbackPushforwardAdjunction A f` (Mathlib/Topology/Sheaves/Functors.lean) take any concrete category `A` with `Category.{w} A`, where X, Y : TopCat.{w}. The requirements are limits and colimits, a forgetful functor that preserves limits and filtered colimits, and reflection of isomorphisms. Examples are `AddCommGrpCat.{v}` and `ModuleCat.{v} R`.

So the module's remark that `Type v` is "required by the current `TopCat.Sheaf.pullback` API" is wrong. Only the universe matching is required, not the restriction to `Type`. The textbook statement holds for sheaves with values in any such category. That includes sheaves of abelian groups, which are what this sheaf-cohomology library uses elsewhere (e.g. `pushforward AddCommGrpCat`). The definition should be parametrized by `A`. Mathlib has no ready-made counterpart for this isomorphism.

### [`CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenCohomology.lean#L476-L484) — `formal-frontier-0032`

Snippet: `samples/formal-frontier/formal-frontier-0032.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical natural isomorphism (F|_U)|_V ≅ F|_V, natural in F, between restricting a sheaf to the over-site of U and then along V ⟶ U, and restricting directly to V. Inferred from the docstring and the name.
- **mathlib_counterpart**: CategoryTheory.Sheaf.pushforwardOverMapIso
- **explanation**: The body is `NatIso.ofComponents (fun F => Sheaf.pushforwardOverMapIso F i)`, with naturality proved by `ext; rfl`. `restrictToOver U` is an abbreviation for `(Opens.grothendieckTopology X).overPullback AddCommGrpCat U`, and `inclusionRestrict i` for `....overMapPullback AddCommGrpCat i`. Mathematically this is the right transitivity isomorphism for restriction.

But `GrothendieckTopology.overPullback`, `GrothendieckTopology.overMapPullback` and `Sheaf.pushforwardOverMapIso` (whose components are identities) are all defined in Mathlib for an arbitrary site (C, J), any coefficient category A and any morphism f : X ⟶ Y. The naturality proof works verbatim in that setting. The construction uses nothing about topological spaces, open sets or AddCommGrpCat, and the sheafification and local-bijectivity hypotheses play no role.

The natural statement is J.overPullback A Y ⋙ J.overMapPullback A f ≅ J.overPullback A X for any site and coefficient category. Mathlib already provides it objectwise as `Sheaf.pushforwardOverMapIso`, together with related coherences such as `overMapPullbackComp`. Specialising to Opens X and abelian-group coefficients is therefore narrower than the construction's natural generality.

### [`AlgebraicGeometry.unitriangularGroupSchemeBaseChangeTowerIso`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularBaseChangeCoherence.lean#L77-L91) — `formal-frontier-0051`

Snippet: `samples/formal-frontier/formal-frontier-0051.lean`

- **verdict**: `too_narrow`
- **intended_object**: For a tower of rings R → S → T, the canonical transitivity-of-base-change isomorphism of group schemes G_T ≅ (G_S)_T. Here G is the unitriangular group scheme U_ι over Spec R. This comes from the docstring ("canonical group-object compositor for pullback over a scalar tower") and from how the iso is used in `unitriangularGroupSchemeBaseChangeIso_tower`.
- **mathlib_counterpart**: CategoryTheory.Over.pullbackComp
- **explanation**: The construction is correct. The body is an `eqToIso` (from `unitriangularBaseMap_comp`), followed by `Functor.mapGrpNatIso (Over.pullbackComp g f)` applied at G, followed by `Functor.mapGrpCompIso` applied at G. This is the canonical isomorphism pullback_{f≫g}(G) ≅ pullback_f(pullback_g(G)) in group objects, so it does define the intended canonical iso.

But the body never uses anything specific to `unitriangularGroupScheme R ι`. The same expression works verbatim for any group object G : Grp (Over (Spec R)). More generally it works for any group object in Over Z of a category with pullbacks, along any composable f, g, where the eqToIso only needs f ≫ g = h. The hypotheses `[Fintype ι] [LinearOrder ι]` and the choice of the unitriangular group serve only to name the object at which the natural isomorphism is evaluated.

Transitivity of base change is a general fact about pullbacks of (group) schemes, and Mathlib supplies it in full generality through `Over.pullbackComp` combined with `Functor.mapGrpNatIso` and `Functor.mapGrpCompIso`. This definition writes that general construction out for one particular group scheme. Its content does not need that special setting, so it is narrower than the natural generality of the notion.

### [`AlgebraicGeometry.Scheme.Hom.kernImage`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/KernImage.lean#L33-L35) — `formal-frontier-0110`

Snippet: `samples/formal-frontier/formal-frontier-0110.lean`

- **verdict**: `too_narrow`
- **intended_object**: For a closed map π : E → B, the open set of B made of the points whose whole π-fibre lies in a given open W ⊆ E. Equivalently, it is B \ π(E \ W), the largest open V with π⁻¹(V) ⊆ W (the right adjoint of preimage on opens). This comes from the docstring and the module documentation.
- **mathlib_counterpart**: Set.kernImage
- **explanation**: The definition is mathematically correct. The carrier is `Set.kernImage π W = {b | ∀ e, π e = b → e ∈ W}`, which is exactly the set of points whose fibre lies in W. Empty fibres are included, which is the standard convention. Openness follows from `isClosedMap_iff_kernImage` applied to the closed-map hypothesis.

However, nothing about schemes is used. The body only needs:
- the underlying map of topological spaces, `π : E → B`;
- the fact that it is a closed map (continuity is not even needed for openness);
- `W` being open.

So the construction makes sense, unchanged, for any closed map f : X → Y of topological spaces, as a map `TopologicalSpace.Opens X → TopologicalSpace.Opens Y` with the Galois connection `Opens.comap f ⊣ kernImage f`. The listed properties (`le_kernImage_iff`, `kernImage_gc`, `kernImage_mono`, `kernImage_top`) are all purely topological too. Only the extra lemma `le_kernImage_preimage_iff_existsUnique` uses scheme structure, and it could be stated for a scheme-level specialisation of a general topological definition.

Mathlib has the set-level construction `Set.kernImage` and the openness criterion `isClosedMap_iff_kernImage` in full topological generality, but no `Opens`-bundled version. Defining the bundled open only for scheme morphisms therefore restricts a topological construction to a special setting that its content does not need. The natural form would be a general `TopologicalSpace.Opens` (or `IsClosedMap`) construction, with a scheme-level wrapper if desired, as Mathlib does with `Opens.comap` and `⁻¹ᵁ`.

### [`Bass.coordinateHyperplaneEquiv`](https://github.com/FormalFrontier/stable-range/blob/c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e/StableRange/RowKernel.lean#L148-L167) — `formal-frontier-0165`

Snippet: `samples/formal-frontier/formal-frontier-0165.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical linear isomorphism between the coordinate hyperplane {x ∈ Rⁿ : xᵢ = 0} (the kernel of the i-th coordinate projection) and R^{indices ≠ i}, i.e. functions on the other coordinates. Inferred from the docstring and the name.
- **mathlib_counterpart**: LinearMap.iInfKerProjEquiv
- **explanation**: The definition is mathematically correct. It takes Mathlib's `LinearMap.iInfKerProjEquiv` with I = {j | j ≠ i} and J = {i}, and composes it with `LinearEquiv.ofEq`, which identifies ker(proj i) with ⨅ j ∈ {i}, ker(proj j). The result is the isomorphism ker(proj i) ≃ ({j // j ≠ i} → R), which is the intended object.

It is stated only for the index type `Fin n` and the constant family R, though. The body uses neither. The disjointness and covering arguments work for any index type ι (with decidable equality, which is supplied here by `classical` anyway). The same construction also works for any family φ : ι → Type of R-modules: it gives ker(proj i) ≃ₗ (∀ j : {j // j ≠ i}, φ j). At the very least it works for a constant module M in place of R. The docstring itself calls this a specialization of Mathlib's general equivalence.

Inside this library the result is only used with the row spaces Fin n → R. Still, a coordinate hyperplane being isomorphic to the product over the remaining coordinates is a statement about arbitrary product modules, and Mathlib states the comparable `iInfKerProjEquiv` for arbitrary ι and families φ. Specializing it to `Fin n` and R is therefore narrower than the natural generality, so the verdict is too_narrow rather than incorrect.

### [`GradedRing.Veronese.reindex`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/Veronese.lean#L146-L147) — `formal-frontier-0180`

Snippet: `samples/formal-frontier/formal-frontier-0180.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CategoryTheory.NatTrans.IsPointwiseSubgroup.internalInclusion`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupObject/FunctorCategory.lean#L318-L320) — `formal-frontier-0187`

Snippet: `samples/formal-frontier/formal-frontier-0187.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.Modules.tensorFunctor`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/ModuleTensor.lean#L60-L73) — `formal-frontier-0192`

Snippet: `samples/formal-frontier/formal-frontier-0192.lean`

- **verdict**: `too_narrow`
- **intended_object**: The tensor product of O_X-modules: (M, N) ↦ M ⊗_{O_X} N, the sheafification of the presheaf U ↦ M(U) ⊗_{O_X(U)} N(U), as a bifunctor on O_X-modules (from the docstring, the module doc and the companion defs `tensor`/`tmul`/`tensorSymm`).
- **explanation**: The definition is mathematically correct. It sends M, N to their underlying presheaves of modules, takes Mathlib's pointwise tensor product of presheaves of modules over a presheaf of commutative rings (sections M(U) ⊗_{O_X(U)} N(U)), and then applies Mathlib's sheafification of presheaves of modules along 𝟙 of the structure sheaf. This is exactly the standard tensor product of O_X-modules, functorial in both arguments. However, nothing in the body uses that X is a scheme. `X.Modules` is just `SheafOfModules X.ringCatSheaf`; the pointwise tensor product only needs a presheaf of commutative rings (`PresheafOfModulesOfCommRing.monoidalCategory` is stated for a general site); and `PresheafOfModules.sheafification` only needs a site with sheafification. The literature defines this tensor product for arbitrary ringed spaces, and more generally for sheaves of commutative rings on a site (Hartshorne II.5; Stacks Project, modules on ringed spaces and sites). The same three-step construction applies verbatim to `SheafOfModules R` for any sheaf of commutative rings R on such a site, or at least on any ringed space. This Mathlib version has no sheafified tensor product of `SheafOfModules` to cite. Still, the natural generality is broader than schemes, so the definition is too narrow. Mitigating point: Mathlib itself specialises `SheafOfModules` to schemes as `Scheme.Modules`, so a scheme-focused library building API on that type is reasonable; hence moderate rather than full confidence in this verdict.

### [`ContinuousCohomology.CorestrictionTransversal.crossedRestrict`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/Corestriction.lean#L711-L722) — `formal-frontier-0199`

Snippet: `samples/formal-frontier/formal-frontier-0199.lean`

- **verdict**: `too_narrow`
- **intended_object**: The restriction map on continuous 1-cocycles (continuous crossed homomorphisms) Z¹_cts(G, X) → Z¹_cts(H, X|_H), f ↦ f|_H, for a subgroup H of a topological group G. The docstring and name say this, and the library uses it with corestriction and transfer.
- **explanation**: The construction itself is correct. It composes a continuous crossed homomorphism f : G → X with the subgroup inclusion H → G, which gives a continuous map H → X. Then it restricts the codomain to `continuousCrossedHom (TopRep.res H.subtype X)`. The cocycle identity f(gh) = g·f(h) + f(g) for g, h ∈ H follows directly from the identity on G. The result is k-linear and continuous, since it is built from `ContinuousMap.compCLM`.

However, the definition only accepts `H : OpenSubgroup G`, and the body never uses openness. It needs only `H.subtype : H →* G`, used by `TopRep.res`, which accepts any monoid hom, and `continuous_subtype_val`, which holds for any subgroup with the subspace topology. The definition does not even use the `IsTopologicalGroup G` assumption. The same code would compile verbatim for any `H : Subgroup G`. More generally, it would work as a pullback along any continuous group homomorphism φ : H → G.

The literature defines restriction of continuous cochains, cocycles and cohomology for arbitrary (closed) subgroups of topological groups. For example, Neukirch–Schmidt–Wingberg defines it for closed subgroups of profinite groups. Finite index and openness are needed only for corestriction and transfer, not for restriction. So limiting it to open subgroups is an artificial narrowing of a construction that makes sense in general.

The narrowing is convenient for this file, where H is always open of finite index. But as a definition of the restriction map, it sits at narrower generality than its natural one.

### [`AlgebraicGeometry.UnitriangularStageNormality.stageRing`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularStageNormality.lean#L51-L51) — `formal-frontier-0203`

Snippet: `samples/formal-frontier/formal-frontier-0203.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`GradedLocalization.zeroComponent`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/Localization.lean#L93-L105) — `formal-frontier-0204`

Snippet: `samples/formal-frontier/formal-frontier-0204.lean`

- **verdict**: `too_narrow`
- **intended_object**: The degree-zero part of the localization A_M of a graded ring A at a submonoid M of homogeneous elements, viewed as a subring of A_M: the fractions a/b with b ∈ M ∩ A_j and a ∈ A_j for some degree j (docstring, and the file's equivalence with `HomogeneousLocalization`).
- **mathlib_counterpart**: HomogeneousLocalization
- **explanation**: The content is right. The carrier is `component M 0`, the set of z = mk a b with a ∈ 𝒜 (0 + j), b ∈ 𝒜 j and b ∈ M. That is exactly the set of degree-zero fractions. It is closed under 0, 1, +, − and ·, so it is a subring. The file also proves that it is isomorphic to Mathlib's `HomogeneousLocalization 𝒜 M`.

The setting is narrower than it needs to be. The index type ι is required to be an `AddCommGroup`, because of a file-wide `variable` that the later parts of the file need: building the full grading on A_M uses k − j. Neither `zeroComponent` nor `component`, which it is built from, uses negation or subtraction in ι. Membership only involves i + j, and the closure proofs only use associativity and commutativity of addition. So the definition works unchanged for any `AddCommMonoid ι`.

Mathlib defines the same object, `HomogeneousLocalization 𝒜 x` (the degree-zero part of A_x, described in Mathlib as a subring of Aₓ), for `[AddCommMonoid ι]`. Requiring a group leaves out the most important case, ℕ-graded rings, where this degree-zero ring is the basic building block of the Proj construction. So the definition is correct but too narrow: it should be stated for `AddCommMonoid ι`, or given as the range of `HomogeneousLocalization.val`.

### [`AlgebraicGeometry.RingedSpace.ClosedPointHom.globalSectionsMap`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/ClosedPointHom.lean#L61-L65) — `formal-frontier-0219`

Snippet: `samples/formal-frontier/formal-frontier-0219.lean`

- **verdict**: `too_narrow`
- **intended_object**: Given a morphism of ringed spaces f : X → Spec R, this is the ring map it induces on global sections, R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X), i.e. Γ(f) precomposed with the canonical isomorphism R ≅ Γ(Spec R). I read this off the docstring and from how the file uses it: it is the inverse of the classification `equiv`.
- **mathlib_counterpart**: AlgebraicGeometry.SheafedSpace.Γ
- **explanation**: The body is the canonical isomorphism `StructureSheaf.globalSectionsIso R : R ≅ Γ(Spec R)` composed with `f.hom.c.app (op ⊤)`, which is the action of f on global sections. This is the right map. It agrees with Mathlib's global-sections functor `SheafedSpace.Γ.map f.op`, precomposed with `globalSectionsIso`.

The problem is generality. The section's `variable` line includes `[IsLocalRing R]`. Lean auto-includes an instance-implicit variable once `R` appears in the statement, so `globalSectionsMap` requires R to be a local ring. The body never uses this: `globalSectionsIso` and `f.hom.c.app (op ⊤)` work for any commutative ring R. The library itself shows this. The next lemma, `globalSectionsMap_eq_transport`, is stated with `omit [IsLocalRing R] in`, so it holds for arbitrary R. But it can only mention `globalSectionsMap` because Lean re-adds the instance when a definition needs it, so the authors could not actually drop it there.

Locality only matters for the other definitions in the file: `base`, which sends everything to the closed point, and `hom`. The map on global sections induced by a morphism to Spec R is a standard notion for every commutative ring R. Mathlib defines the global-sections functor in full generality. So requiring a local ring is an unnecessary restriction.

### [`ContinuousCohomology.cochainsZeroIso`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/DegreeOne.lean#L398-L400) — `formal-frontier-0245`

Snippet: `samples/formal-frontier/formal-frontier-0245.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.infinitesimalAdditiveTranslationIso`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/InfinitesimalAdditiveTranslation.lean#L149-L156) — `formal-frontier-0278`

Snippet: `samples/formal-frontier/formal-frontier-0278.lean`

- **verdict**: `too_narrow`
- **intended_object**: The isomorphism of schemes over Spec K between Spec K[T]/(T^{p^m}) (the scheme underlying α_{p^m}) and Spec K[U]/(U^{p^m}−1) (the roots-of-unity scheme μ_{p^m}). It is induced by the substitution U = 1 + T in characteristic p and asserts no compatibility with the group laws (Milne, Algebraic Groups, item 2.5). Inferred from the docstring and the module documentation.
- **explanation**: The construction is correct. The coordinate maps U ↦ 1+T and T ↦ U−1 are well defined because (1+x)^{p^m} = 1 + x^{p^m} holds in characteristic p, and they are mutually inverse. Taking algSpec of the .op of the algebra isomorphism from the μ side to the α side gives an isomorphism from the α-scheme to the μ-scheme over Spec K, matching the stated type. However, nothing in it uses that K is a field. The characteristic-p lemmas (translation_char_target, translation_add_pow) only use CommRing and CharP K p, and AdjoinRoot.liftAlgHom and algSpec work over any commutative ring. The helper equivalences rootsOfUnityCoordinateAlgEquiv, additivePowerCoordinateAlgEquiv and Ideal.quotientEquivAlg are already stated for [CommRing K]. So are both schemes being connected, infinitesimalAdditiveUnderlyingScheme and rootsOfUnityScheme, whose module docs say they are "extended from fields to commutative bases of prime characteristic". That the underlying schemes of α_{p^m} and μ_{p^m} are isomorphic is standard over any base of characteristic p (any 𝔽_p-algebra); only Milne's presentation happens to be over a field. Replacing [Field K] with [CommRing K] (keeping [CharP K p]) would make the definition go through at the generality its own building blocks already have. The restriction to a field is therefore unnecessary.

### [`QuadraticAlgebra.adjoinRootEquivOfRoot`](https://github.com/FormalFrontier/quadratic-algebras/blob/85a6b1bc79989b524a4ecdae6cce17b712a7bd2d/QuadraticAlgebras/RealClosedAdjoinRoot.lean#L48-L78) — `formal-frontier-0342`

Snippet: `samples/formal-frontier/formal-frontier-0342.lean`

- **verdict**: `too_narrow`
- **intended_object**: An R-algebra isomorphism R[X]/(p) ≅ R[i] = QuadraticAlgebra R (-1) 0 that sends the class of X to a chosen root z of p, for an irreducible quadratic p over a field R. Inferred from the docstring, the name and the module documentation.
- **mathlib_counterpart**: AdjoinRoot.equiv'
- **explanation**: The map itself is correct. It is `AdjoinRoot.liftAlgHom` sending `root p` to `z`. It is injective because `AdjoinRoot p` is a field (p is irreducible) and the target is nontrivial. It is bijective because both sides have dimension 2 over R. This is the standard isomorphism, and the companion lemmas confirm that it sends the root to `z` and the class of g to g(z).

The problem is that the parameters `(-1, 0)` play no role in the construction or its proof. The only fact used about the target is `QuadraticAlgebra.finrank_eq_two (-1) 0`, and the general lemma `QuadraticAlgebra.finrank_eq_two a b` holds for every a and b. So the same definition and the same proof work word for word for any `QuadraticAlgebra R a b`, and even for any R-algebra A with finrank_R A = natDegree p. In general: for an irreducible p over a field and a root z of p in an R-algebra of the same finite dimension, `liftAlgHom` gives an isomorphism. Mathlib already has this kind of construction in general form as `AdjoinRoot.equiv'`, which builds `AdjoinRoot g ≃ₐ[R] S` from a power basis of S and matching roots.

Fixing the target to ℝ-style complex numbers R(√-1) is only needed for the later real-closed application (`adjoinRootEquivOfIrreducible`). That application needs the target to be algebraically closed, but this definition does not use it. So the definition is a correct special case of a construction whose natural setting is an arbitrary quadratic algebra `QuadraticAlgebra R a b`, or more generally any finite-dimensional algebra of dimension deg p.

### [`MvPolynomial.weightedAevalGradedHom`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/WeightedEvaluation.lean#L50-L56) — `formal-frontier-0354`

Snippet: `samples/formal-frontier/formal-frontier-0354.lean`

- **verdict**: `too_narrow`
- **intended_object**: The evaluation map S₀[X_i : i ∈ ι] → S, X_i ↦ x_i, where S₀ is the degree-zero part of the graded ring S, X_i has weight w_i and x_i is homogeneous of degree w_i. It is bundled as a graded (degree-preserving) ring homomorphism from the weighted-graded polynomial ring to S. Inferred from the docstring, the module doc and the uses in the same file.
- **explanation**: The body is right: it takes the ring hom underlying `aeval (fun i => (x i : S))` and proves it maps weighted-homogeneous polynomials of degree n into 𝒮 n. That is exactly the graded evaluation homomorphism. I see no correctness issue.

The problem is generality. Both the grading of S and the weights are fixed to ℕ (`𝒮 : ℕ → σ`, `w : ι → ℕ`). Nothing in the construction uses ℕ:
- Mathlib defines `weightedHomogeneousSubmodule`, `weightedDecomposition` and `weightedGradedAlgebra` for weights in any additive commutative monoid M; the graded algebra structure also needs `DecidableEq M`.
- `GradedRingHom` (`→+*ᵍ`) works for any index type.
- The degree-preservation proof only uses `SetLike.prod_pow_mem_graded`, `SetLike.GradedMul.mul_mem` and `SetLike.GradeZero.algebraMap_apply`. All three hold for any additive-monoid grading.

So the same definition makes sense, with the same proof, for an M-graded ring S and weights w : ι → M. This is the generality of Mathlib's weighted graded algebra. The library itself also states some of its graded-ring material for a general index type ι, e.g. in `HomogeneousLifts`.

ℕ-weights are the most common case in practice (weighted projective spaces, Veronese arguments), and the downstream uses in this library are ℕ-graded. Still, the construction does not need the special setting, so it is narrower than the natural one. Mathlib has no bundled graded version of this evaluation map; the underlying ring map is `MvPolynomial.aeval`.

### [`AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/FiniteTypePoints.lean#L346-L356) — `formal-frontier-0382`

Snippet: `samples/formal-frontier/formal-frontier-0382.lean`

- **verdict**: `too_narrow`
- **intended_object**: The anti-equivalence between finitely generated K-algebras and affine schemes locally of finite type over Spec K, given by A ↦ Spec A. The docstring and the module documentation (Milne, Algebraic Groups 1.4 / A.33) say so.
- **explanation**: The functor itself is correct. `fgAlgToLftAffine` sends A to Spec A over Spec K, viewed as an object of `lftAffineOver K`, the costructured arrows `Spec R → Spec K` that are locally of finite type. Full faithfulness comes from `algSpec.fullyFaithful`. Essential surjectivity (`finiteAlgSpecOver_covers_affine`) works as follows: write the structure map as Spec φ, use `HasRingHomProperty.Spec_iff` to turn local finite type of Spec φ into `RingHom.FiniteType φ`, and so obtain an object of `FGAlgCat K`. So this really is the intended equivalence.

None of these steps uses that K is a field. The equivalence holds over any commutative ring R:
- Mathlib's `FGAlgCat R` is defined for an arbitrary `CommRing R`.
- `algSpec` and `Spec.fullyFaithful` work for any base.
- The argument linking `LocallyOfFiniteType` to `RingHom.FiniteType` works for any ring.

In the literature, "finitely generated R-algebras are dual to affine schemes of finite type over Spec R" is stated over an arbitrary base ring. The field matters only in Milne's later use of the result (algebraic groups over a field), not in this equivalence. So the definition is a faithful special case of a statement whose natural generality is a commutative ring R (or `R : CommRingCat`), and K should be replaced by R. I found no equivalence in this commit of Mathlib that already packages exactly this statement, so no counterpart is given.

### [`Subalgebra.IsFiniteEtale`](https://github.com/FormalFrontier/finite-etale-algebras/blob/4cd253af5e6ac472644ac7058c1ce00a8ee3a2bf/FiniteEtaleAlgebras/MaximalSubalgebra.lean#L65-L68) — `formal-frontier-0394`

Snippet: `samples/formal-frontier/formal-frontier-0394.lean`

- **verdict**: `too_narrow`
- **intended_object**: The predicate that a subalgebra A of a commutative K-algebra R is a finite étale K-algebra, i.e. finite as a K-module and étale over K (from the docstring and the module doc on maximal finite étale subalgebras).
- **mathlib_counterpart**: CommAlgCat.FiniteEtale
- **explanation**: The body is `Algebra.IsFiniteEtale K A`. The library defines that predicate in the same file as `Module.Finite K A ∧ Algebra.Etale K A`, for any `CommRing K`. This is the standard notion of a finite étale algebra, so the predicate is mathematically correct, including in degenerate cases such as the zero ring and `⊥`. However, the `variable` line forces `[Field K]`, and the body uses nothing about K being a field. Mathlib's `Module.Finite` and `Algebra.Etale`, its bundled category `CommAlgCat.FiniteEtale R`, and the library's own `Algebra.IsFiniteEtale` are all stated over an arbitrary commutative ring. "Finite étale subalgebra" is a standard notion over any commutative base ring. The field hypothesis is needed only for the file's theorems (e.g. `of_surjective` via `FormallyEtale.of_formallyUnramified_of_field`, and closure of finite étale subalgebras under suprema), not for the predicate itself. So the predicate should be stated for `[CommRing K]`; restricting it to fields is an unnecessary narrowing.

### [`CategoryTheory.Functor.evalSectionToEventualRange`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/MittagLeffler.lean#L89-L92) — `formal-frontier-0466`

Snippet: `samples/formal-frontier/formal-frontier-0466.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical evaluation map from the compatible sections (inverse limit) of a functor F to types into F(i), with codomain restricted to the eventual range (stable image) of F at i, i.e. x ↦ x(i). Inferred from the docstring ("Evaluation of a compatible section lands in the eventual range"), the name, and the module docstring.
- **explanation**: The body sends x to ⟨x.val i, _⟩ and proves membership in the eventual range via mem_eventualRange_iff, taking x.val k as the preimage under F.map g by the section property. That is mathematically correct. However, it uses only Functor.sections, Functor.eventualRange and mem_eventualRange_iff. In Mathlib (CategoryTheory/CofilteredSystem.lean) all three are defined for an arbitrary category J and functor F : J ⥤ Type v, and so are the related constructions toEventualRanges and toEventualRangesSectionsEquiv. The definition instead fixes the index category to Jᵒᵖ for a preorder J, and nothing in the body uses the preorder structure: no thinness, directedness or order. The preorder, directedness and countable-cofinality hypotheses are needed only for the subsequent surjectivity theorem, not for the map. The same definition makes sense verbatim for any category J, which is the generality in which Mathlib states eventual ranges, so the definition is too narrow. Mathlib has no declaration for this exact map; toEventualRangesSectionsEquiv is the closest related one.

### [`MvPolynomial.localizedCoordinateForwardBase`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/LocalizedCoordinateQuotient.lean#L89-L91) — `formal-frontier-0517`

Snippet: `samples/formal-frontier/formal-frontier-0517.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenCohomology.lean#L727-L735) — `formal-frontier-0574`

Snippet: `samples/formal-frontier/formal-frontier-0574.lean`

- **verdict**: `too_narrow`
- **intended_object**: The functor that sends an open U of X to the free abelian sheaf ℤ_U = a(ℤ[h_U]), the sheafification of the free abelian presheaf on the representable presheaf h_U (equivalently j_!ℤ). It represents cohomology, since H^n(U,F) = Ext^n(ℤ_U, F). This reading comes from the docstring ("sheafified free-Yoneda cohomology source, functorial in the open") and from how the library uses it.
- **mathlib_counterpart**: CategoryTheory.Sheaf.cohomologyPresheafFunctor
- **explanation**: The body is `yoneda ⋙ (whiskeringRight).obj AddCommGrpCat.free ⋙ presheafToSheaf J AddCommGrpCat`. This does give the intended functor U ↦ a(ℤ[Hom(-,U)]) on opens, with the obvious maps. So the definition is mathematically correct.

But the body uses nothing specific to topological spaces. It only needs a category C, a Grothendieck topology J on C, and `HasSheafify J AddCommGrpCat`. The free abelian sheaf on a representable, C ⥤ Sheaf J Ab, is the standard construction for any site; it is the source in the Ext-description of sheaf cohomology on a site. Mathlib uses exactly this composite, for an arbitrary site (C, J), inside `CategoryTheory.Sheaf.cohomologyPresheafFunctor` (Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean, lines 72–76). Mathlib also has the object-level version, `CategoryTheory.Sheaf.freeYoneda J X M`, for a general site.

Restricting to `Opens.grothendieckTopology X` for a `TopCat` X therefore writes out, in one particular setting, a construction that makes sense, and already appears in Mathlib, for arbitrary sites. That makes the definition faithful in content but narrower than its natural generality.

### [`AlgebraicGeometry.finiteAlgSpec`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/FiniteTypePoints.lean#L133-L136) — `formal-frontier-0642`

Snippet: `samples/formal-frontier/formal-frontier-0642.lean`

- **verdict**: `too_narrow`
- **intended_object**: The functor Spec : (finitely generated K-algebras)^op → Sch/Spec K, which sends a finitely generated K-algebra A to Spec A with its structure morphism to Spec K. This comes from the docstring, the name and the module doc (Milne, Algebraic Groups 1.4 / A.33).
- **mathlib_counterpart**: AlgebraicGeometry.algSpec
- **explanation**: The body composes the inclusion `FGAlgCat K ⥤ CommAlgCat K` (taken opposite) with Mathlib's `algSpec (.of K) : (CommAlgCat K)ᵒᵖ ⥤ Over (Spec K)`. Mathematically this is the correct object: Spec, restricted to finitely generated K-algebras, landing in schemes over Spec K.

The definition never uses the hypothesis `[Field K]`, though. Mathlib defines `FGAlgCat R` for any `CommRing R`, and `algSpec R` for any `R : CommRingCat`. So the same body, `(ObjectProperty.ι _).op ⋙ algSpec R`, typechecks over an arbitrary commutative base ring R. Spec on finite-type R-algebras, viewed as schemes over Spec R, is a standard notion over any base ring. The companion results also hold over any ring R:
- full faithfulness, which comes from `algSpec.fullyFaithful` together with the full subcategory inclusion;
- the finite-type structure map, since Spec of a finite-type R-algebra is locally of finite type over Spec R.

The field assumption only matters for the Milne-specific results elsewhere in the file. It plays no part in this construction. Restricting from commutative rings to fields is the kind of narrowing the guidelines describe ("for one specific ring when any commutative ring works", "on ℝ when any field would do"). Mathlib has no ready-made restricted functor, but the general ingredients `FGAlgCat R` and `AlgebraicGeometry.algSpec R` both exist for any commutative ring.

### [`Matrix.UnitriangularGroup.elementary`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass.lean#L40-L50) — `formal-frontier-0646`

Snippet: `samples/formal-frontier/formal-frontier-0646.lean`

- **verdict**: `too_narrow`
- **intended_object**: The elementary unipotent matrix (transvection) e_{ij}(a) = 1 + a·E_{ij} with i < j, seen as an element of the group of upper unitriangular matrices over a commutative ring R. This comes from the docstring and from how the file uses it (Steinberg commutator relation, lower central series of the unitriangular group).
- **mathlib_counterpart**: Matrix.transvection
- **explanation**: The definition builds the right element: the matrix `1 + Matrix.single i j a` (via the library's `GeneralLinearGroup.elementaryUnit`), together with proofs that it is upper triangular and has 1s on the diagonal. So the content is correct.

It is stated only for the index type `Fin n` and for `R : Type` (universe 0). The library's own `Matrix.UnitriangularGroup` (AlgebraicGroups/GroupScheme/Unitriangular.lean) is defined for any `n : Type u` with `[Fintype n] [LinearOrder n]` and any `R : Type u`. The body uses nothing specific to `Fin`. `elementaryUnit` only needs `i ≠ j`. Upper-triangularity comes from `blockTriangular_one` and `blockTriangular_single hij.le`, which only need the order. The diagonal argument only needs `i < j → i ≠ j`.

So the same construction, word for word, makes sense for any finite linearly ordered index type, which is the generality of the ambient `UnitriangularGroup`. The later nilpotency-class theorem in this file does use `Fin n` coordinates such as `⟨0, _⟩` and `⟨k, _⟩`. That is a need of that theorem, not of this definition.

Mathlib has no unitriangular group. At matrix level it has the same element as `Matrix.transvection i j c = 1 + single i j c`, stated for an arbitrary index type. Restricting to `Fin n` when any index type works is exactly the too-narrow case.

### [`GradedRing.Veronese.CoherentTail.TailEquiv.pieceHom`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/CoherentTailVeronese.lean#L60-L61) — `formal-frontier-0650`

Snippet: `samples/formal-frontier/formal-frontier-0650.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`GaloisDescent.fixedScalarExtensionEquiv`](https://github.com/FormalFrontier/finite-etale-algebras/blob/4cd253af5e6ac472644ac7058c1ce00a8ee3a2bf/FiniteEtaleAlgebras/SemilinearDescent.lean#L333-L344) — `formal-frontier-0658`

Snippet: `samples/formal-frontier/formal-frontier-0658.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Galois descent (Speiser) isomorphism: for a finite Galois extension L/k with group G, the canonical L-linear map L ⊗_k V^G → V, l ⊗ v ↦ l·v, is an isomorphism. Here it is stated only for V = L ⊗_k R with the coefficientwise action σ ↦ σ ⊗ id. Inferred from the docstring ("Semilinear descent for the coefficientwise action on a tensor product"), the module doc and the name.
- **explanation**: The definition is mathematically correct. The forward map `fixedScalarExtension` is l ⊗ w ↦ l • w. The inverse `traceDualInverse` is the usual trace-dual averaging x ↦ ∑_i b_i ⊗ ∑_σ σ(b_i^∨)·σ(x). Both composites are proved to be the identity, so it is the canonical descent isomorphism L ⊗_k V^G ≅ V for V = L ⊗_k R.

However, nothing in the construction or its proof uses the special shape of V. The ingredients are:
- `traceAverage` and `coefficientwise_traceAverage`, which need only that the action is a group action by σ-semilinear additive maps (`coefficientwise_mul`, `coefficientwise_smul`);
- `traceDual_orthogonality` and `trace_eq_sum_automorphisms`, which concern only L/k;
- `traceAverage_smul_fixed`, which only uses that w is fixed.

`fixed_iff_mem_range_includeRight`, the only place where the tensor structure (a basis of R) matters, is not used by this equivalence. So the same definition and proof work for any L-vector space (indeed any L-module) V with a semilinear action of Gal(L/k). That general statement is semilinear Galois descent, or Speiser's lemma, which is what the docstring names.

Even inside the tensor-product setting, the hypotheses `[CommRing R] [Algebra k R]` are only there because `coefficientwise` is built with `Algebra.TensorProduct.map`. For this equivalence a k-module structure on R would be enough, e.g. using `LinearMap.rTensor`.

Mathlib has no general Galois descent equivalence (a grep for Galois descent, semilinear descent and Speiser in Mathlib found nothing). So the natural generality is a semilinear G-module V over L, and this definition writes the construction out only for V = L ⊗_k R with R a commutative k-algebra.

### [`ContinuousMap.integralLinearMap`](https://github.com/FormalFrontier/complex-analysis/blob/2c0ad1d2ce6d2f815930d64428d66618cb9f122d/ComplexAnalysis/MeasureTheory/Integral/ContinuousMap.lean#L42-L50) — `formal-frontier-0697`

Snippet: `samples/formal-frontier/formal-frontier-0697.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Bochner integral f ↦ ∫ f dμ as a linear map on the space C(X, F) of continuous functions on a compact space X, with values in a Banach space F, for a finite Borel measure μ. Inferred from the docstring and the module documentation.
- **explanation**: The body is correct. It sends f to ∫ x, f x ∂μ. Additivity follows from `ContinuousMap.integrable` and `integral_add`, and homogeneity from `integral_smul`. Compactness and finiteness of μ are used only to get integrability, which is the standard setting for this map.

The problem is the scalar field: it is fixed to ℂ. The construction uses ℂ only to get the ℝ-structure the Bochner integral needs and to make `integral_smul` apply. `integral_smul` holds for any normed field 𝕜 with `[NormedSpace 𝕜 F]` and `[SMulCommClass ℝ 𝕜 F]`, so the map is 𝕜-linear in that generality (in particular ℝ-linear for any real Banach space F). Nothing in the definition is specific to complex analysis.

Mathlib states its comparable integration maps over a general scalar field:
- `MeasureTheory.L1.integralCLM'` is `(α →₁[μ] E) →L[𝕜] E`;
- `SchwartzMap.integralCLM` is `𝓢(D, V) →L[𝕜] V`;
- `ContinuousMap.toLp` / `BoundedContinuousFunction.toLp` are 𝕜-linear.

So the natural formulation is `C(X, F) →ₗ[𝕜] F` for a general 𝕜, as in those declarations. Mathlib has no direct named counterpart for integration on C(X, F): one could compose `L1.integralCLM' 𝕜` with `ContinuousMap.toLp`, but that is a composite, not a single declaration. Hard-coding ℂ is a needless restriction of a construction that works for any 𝕜, so the definition is too narrow.

### [`TopCat.Sheaf.CommRingForget.canonicalComparison`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/CommRingForget/Pullback.lean#L101-L108) — `formal-frontier-0707`

Snippet: `samples/formal-frontier/formal-frontier-0707.lean`

- **verdict**: `too_narrow`
- **intended_object**: Fix a continuous map g : X → Y. The object is the canonical base-change natural transformation g⁻¹(forget A) → forget(g⁻¹A) between the sheaf-of-sets pullback of the underlying sheaf and the underlying sheaf of the ring-sheaf pullback. It is the mate, under the two adjunctions g⁻¹ ⊣ g_*, of the commutation of the forgetful functor with pushforward. I inferred this from the docstring, the module documentation and the companion `canonicalComponent`.
- **mathlib_counterpart**: CategoryTheory.mateEquiv
- **explanation**: Each component of the definition is `((pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).symm ((underlyingSheaf Y).map (unit of the CommRingCat adjunction at A))`. This is the standard mate of the identity square g_* ⋙ forget = forget ⋙ g_*, and as a construction it is correct.

The construction uses nothing about `CommRingCat` or `Type`. It needs only:
1. the pullback ⊣ pushforward adjunctions in both coefficient categories;
2. sheaf composition along a functor F (`sheafCompose`) commuting with pushforward, which holds definitionally for any F.

So the same definition works word for word for any functor F : C ⥤ D, for any coefficient categories C and D in which `TopCat.Sheaf.pullback` exists. Mathlib's general tool for this kind of transformation is `CategoryTheory.mateEquiv`, applied to the adjunctions and the identity two-square. Mathlib also states the analogous comparison for sheafification for an arbitrary functor F (`sheafComposeNatTrans`).

The library confirms the special setting is not needed: this file is a ring-specialised copy of an additive version (`AbelianForget.Pullback`), so the same construction is duplicated for each coefficient category. Only the later theorem that the comparison is an isomorphism (`canonicalComponent_isIso`) uses specific properties of the forgetful functor on commutative rings (via Kan-extension and sheafification preservation results). The definition itself does not. It therefore fixes one particular functor (forget from commutative rings) where any functor would do, which makes it too narrow.

### [`TopCat.reducedSingularHomologyFunctor`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Reduced.lean#L252-L258) — `formal-frontier-0718`

Snippet: `samples/formal-frontier/formal-frontier-0718.lean`

- **verdict**: `too_narrow`
- **intended_object**: The reduced singular homology functor H̃_n(−; ℤ) : Top → Ab for n ≥ 0: in degree 0 it is the kernel of the augmentation H₀(X) → ℤ, and in positive degrees it is ordinary singular homology. This comes from the docstring and the module header ("Reduced singular homology with integer coefficients").
- **explanation**: **Correctness.** The definition is mathematically correct.
- In degree 0 it is the functor `reducedSingularHomologyZeroFunctor`. On objects this is `kernel (X.singularHomology₀ε integerCoefficients)`, and maps come from `kernel.map`, using naturality of the augmentation.
- In degree n+1 it is Mathlib's `singularHomologyFunctor` with coefficients `integerCoefficients` (ULift ℤ).
- This agrees in every degree n ≥ 0 with the homology of the augmented singular chain complex. That includes the empty space: H₀(∅) = 0, so the kernel is 0, as the augmented complex gives in degree 0. The degree −1 group ℤ for ∅ is excluded by the stated nonnegative convention.

**Generality.** The coefficients are fixed to ℤ, i.e. to `ModuleCat.{u,0} ℤ` with `integerCoefficients`. Nothing in the construction uses ℤ:
- Mathlib's `singularHomologyFunctor C n` and the augmentation `TopCat.singularHomology₀ε X R` are defined for any coefficient object `R` in any suitable preadditive category `C` with coproducts and homology.
- Taking the kernel only needs kernels, which exist in any abelian category such as `ModuleCat R` for any ring.

So the same two-case definition works word for word with an arbitrary coefficient object R. Reduced homology with coefficients in any abelian group or module G is standard in the literature (e.g. Hatcher §2.2, H̃_n(X; G)). The definition writes out, for ℤ only, a construction whose natural setting, and Mathlib's surrounding infrastructure, is general in the coefficients.

Mathlib has no reduced singular homology, so there is no direct counterpart. The verdict is therefore too narrow, not incorrect.

### [`GradedRing.Veronese.CoherentTail.TailEquiv.pieceHomSymm`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/CoherentTailVeronese.lean#L174-L176) — `formal-frontier-0723`

Snippet: `samples/formal-frontier/formal-frontier-0723.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`MvPolynomial.localizedCoordinateForwardAway`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/LocalizedCoordinateQuotient.lean#L97-L99) — `formal-frontier-0756`

Snippet: `samples/formal-frontier/formal-frontier-0756.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Order.Ideal.principalHom`](https://github.com/FormalFrontier/ideal-completion/blob/40e07d50b85ca7b3ad89a4cc19f50972998a2c94/IdealCompletion/OrderIdeal.lean#L29-L45) — `formal-frontier-0761`

Snippet: `samples/formal-frontier/formal-frontier-0761.lean`

- **verdict**: `too_narrow`
- **intended_object**: The principal-ideal embedding a ↦ ↓a from a bounded lattice A into its lattice of order ideals Idl(A), viewed as a bounded lattice homomorphism. Inferred from the docstring and the module doc on ideal completions.
- **explanation**: The map is correct: `principal a` is the down-set ↓a. Mathlib's join of ideals is {x | ∃ i ∈ I, j ∈ J, x ≤ i ⊔ j}, so ↓(a⊔b) = ↓a ⊔ ↓b. The meet is intersection, so ↓(a⊓b) = ↓a ∩ ↓b. Mathlib's lemmas `principal_top` and `principal_bot` give the bounds. So the definition really is a bounded lattice homomorphism.

However, the definition is stated with `[DistribLattice A] [BoundedOrder A]`, and nothing in it uses distributivity. The `map_sup'` proof only uses `le_sup_left`/`le_sup_right` (via `mem_principal_self`) and `sup_le_sup`. The `map_inf'` proof only uses `le_inf_iff`. The bounds come from `principal_top` and `principal_bot`, which hold for any preorder with top or bottom.

Mathlib already provides everything needed in that generality:
- `Lattice (Ideal P)` for `[SemilatticeSup P] [IsCodirectedOrder P]`, which every lattice satisfies;
- `OrderBot (Ideal P)` for `[OrderBot P]`;
- `OrderTop (Ideal P)` for `[IsDirectedOrder P] [Nonempty P]`.

So the same body would compile verbatim with `[Lattice A] [BoundedOrder A]`. It is a standard fact that a ↦ ↓a is a (bounded) lattice embedding of any (bounded) lattice into its ideal lattice. Distributivity is needed only for the frame instance later in this file, not for this homomorphism. The definition is therefore correct but needlessly restricted to distributive lattices.

Mathlib has no bundled version of this map for `Order.Ideal`. The closest analogue is `DedekindCut.principalEmbedding`, which is for a different completion.

### [`UnitriangularCoordinateRing.polynomialQuotient`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/UnitriangularCoordinateRing.lean#L263-L264) — `formal-frontier-0773`

Snippet: `samples/formal-frontier/formal-frontier-0773.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`Algebra.TensorProduct.rightLinearMap`](https://github.com/FormalFrontier/integral-closure/blob/3951c14b1fa0d56eb2c2cbc2acf390794676c055/IntegralClosure/TensorProduct.lean#L38-L49) — `formal-frontier-0785`

Snippet: `samples/formal-frontier/formal-frontier-0785.lean`

- **verdict**: `too_narrow`
- **intended_object**: The base change of a k-linear functional f : l → k along k → A: the A-linear functional on A ⊗_k l given by id_A ⊗ f followed by A ⊗_k k ≅ A, so that a ⊗ b ↦ a · f(b). This comes from the docstring and the name.
- **mathlib_counterpart**: Module.Dual.baseChange
- **explanation**: The definition builds the right map: `AlgebraTensorModule.lift` applied to a ↦ a • (algebraMap ∘ f) sends a ⊗ b to a · algebraMap(f b). That is the base change of the functional f. It is correct, but it is stated with hypotheses it never uses: `Field k`, `Field l`, `Algebra k l` and `CommRing A`. The body only uses that k is a commutative semiring, that l is a k-module (its ring structure and its being a field play no role), and that A is a k-algebra. The docstring itself says neither f 1 = 1 nor multiplicativity is needed. The lemma `rightLinearMap_includeLeft` does use the unit of l, but only through `f 1`, and that is a property of the lemma, not of the construction. Mathlib already has this construction in full generality: `Module.Dual.baseChange A f : Dual A (A ⊗[R] V)` for `CommSemiring R`, any R-module V and a commutative R-algebra A, with `baseChange_apply_tmul : f.baseChange A (a ⊗ₜ v) = f v • a`. It can also be obtained as `AlgebraTensorModule.rid R A A ∘ₗ f.baseChange A`. So the library's definition restates, for fields only, a construction Mathlib provides in general.

### [`ProjectiveSpace.closedPointsEquivOfIso`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/GradedProjIso.lean#L163-L170) — `formal-frontier-0790`

Snippet: `samples/formal-frontier/formal-frontier-0790.lean`

- **verdict**: `too_narrow`
- **intended_object**: The bijection between the sets of closed points of two schemes X and Y induced by an isomorphism X ≅ Y: x ↦ e(x), restricted to closed points. Inferred from the docstring and the companion lemma `closedPointsEquivOfIso_apply_coe`.
- **explanation**: The definition is mathematically correct. It takes the homeomorphism of underlying spaces given by the isomorphism (`Scheme.homeoOfIso e`) and restricts it to `closedPoints`, using that a homeomorphism maps closed singletons to closed singletons. So it does define the intended bijection.

However, it uses nothing about schemes beyond the underlying homeomorphism. Both `closedPoints` (in `Mathlib/Topology/JacobsonSpace.lean`) and the argument (`Homeomorph.isClosed_image`, `Set.image_singleton`) are purely topological. The same construction works for any homeomorphism `X ≃ₜ Y` of topological spaces, giving `closedPoints X ≃ closedPoints Y`. Mathlib defines `closedPoints` at that level, and a Mathlib-style version would be something like `Homeomorph.closedPointsEquiv`. The scheme case would then be that general map applied to `Scheme.homeoOfIso e`.

I searched Mathlib and found no such general declaration. Still, the natural setting for this construction is homeomorphisms of topological spaces, not isomorphisms of schemes. The scheme setting is not needed for anything the definition does, so it is stated more narrowly than its natural generality.

### [`CategoryTheory.Sheaf.OpenCohomology.overConstantSource`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenCohomology.lean#L88-L94) — `formal-frontier-0841`

Snippet: `samples/formal-frontier/formal-frontier-0841.lean`

- **verdict**: `too_narrow`
- **intended_object**: The extension by zero j_!ℤ_U (often written ℤ_U) of the constant sheaf ℤ on the open U to an abelian sheaf on X. It is the left adjoint of restriction applied to the constant sheaf, and it corepresents sections over U. This comes from the docstring ("extension to X of the constant integral sheaf on the over-site at U") and from how the file uses it as the Ext source that corepresents sections over U.
- **explanation**: The body applies the left adjoint of `J.overPullback AddCommGrpCat U` to `(constantSheaf (J.over U) AddCommGrpCat).obj (ULift ℤ)`. That is exactly j_!(ℤ_U), so the construction is mathematically correct. Elsewhere the file proves it corepresents sections over U and is isomorphic to the sheafified free abelian presheaf on yoneda U, which matches the textbook characterisation.

But nothing in the body is specific to topological spaces:
- `GrothendieckTopology.overPullback` is defined in Mathlib for any site (C, J) and any object U : C (`Mathlib/CategoryTheory/Sites/Over.lean`).
- `constantSheaf` makes sense on the over-site `J.over U` of any site.
- The left adjoint exists in general: `Mathlib/CategoryTheory/Sites/Pullback.lean` gives an `IsRightAdjoint` instance for pushforward along a continuous functor (here `Over.forget U`) whenever sheafification exists. The file itself builds it through the general `Functor.sheafPullbackConstruction`.

The object ℤ_U = j_{U!}ℤ is standard for arbitrary sites (e.g. in the Stacks project, where it is the sheafification of the free abelian presheaf on h_U). Mathlib's own sheaf-cohomology API (`Sheaf.H'`, `Sheaf.H`) is stated for an arbitrary site, so the same definition with `Opens.grothendieckTopology X` replaced by a general `J : GrothendieckTopology C` and `U : C` would work unchanged, with the same typeclass hypotheses. Mathlib has no named counterpart for j_!ℤ_U. Fixing the setting to `Opens X` of a `TopCat` is therefore narrower than needed.

### [`UnitriangularStageCoordinateRing.quotientBialgHom`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/UnitriangularStageCoordinateRing.lean#L266-L267) — `formal-frontier-0853`

Snippet: `samples/formal-frontier/formal-frontier-0853.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CategoryTheory.NatTrans.IsPointwiseSubgroup.targetInternalGrp`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupObject/FunctorCategory.lean#L315-L316) — `formal-frontier-0858`

Snippet: `samples/formal-frontier/formal-frontier-0858.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`RingedSpaces.Modules.moduleSheafificationAdjunction`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/SheafChangeOfRings.lean#L75-L81) — `formal-frontier-0931`

Snippet: `samples/formal-frontier/formal-frontier-0931.lean`

- **verdict**: `too_narrow`
- **intended_object**: The sheafification adjunction for modules: for a sheaf of rings 𝒪 on a site, sheafifying presheaves of 𝒪-modules is left adjoint to the forgetful functor from sheaves of 𝒪-modules to presheaves of 𝒪-modules. This comes from the docstring, the name, and how the definition is used to build the tensor/extension-of-scalars adjunction.
- **mathlib_counterpart**: PresheafOfModules.sheafificationAdjunction
- **explanation**: The body just applies Mathlib's `PresheafOfModules.sheafificationAdjunction` with α = 𝟙 (ringSheaf B).obj. The right adjoint `restrictScalars (𝟙 _)` is canonically the forgetful functor, so the object being defined is correct: sheafification ⊣ forget for modules over B.

However, the definition only accepts a sheaf of **commutative** rings `B : Sheaf J CommRingCat`, which is then converted into a sheaf of rings with `forget₂`. Nothing in the construction uses commutativity. The sheafification adjunction for modules is standard over any sheaf of rings. Mathlib already provides it in that generality, and more: for any sheaf of rings R and any locally bijective map α : R₀ ⟶ R.val from a presheaf of rings, `PresheafOfModules.sheafificationAdjunction α`. So this is a re-statement, in a special setting, of a construction Mathlib has in general.

The library restricts to commutative rings because the later tensor-product construction needs them. That is a reason for its other definitions, not something this adjunction needs. So it is a faithful but needlessly specialized wrapper: too_narrow.

### [`AlgebraicGeometry.closedPointsHomeomorphOfIso`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/ClosedPoints.lean#L112-L117) — `formal-frontier-0945`

Snippet: `samples/formal-frontier/formal-frontier-0945.lean`

- **verdict**: `too_narrow`
- **intended_object**: The homeomorphism between the subspaces of closed points of X and Y that a scheme isomorphism X ≅ Y induces by restricting its underlying homeomorphism (from the docstring and how the file uses it for the inversion and translation homeomorphisms).
- **explanation**: The body gives the right map. It takes the underlying homeomorphism `e.schemeIsoToHomeo` and restricts it to `closedPoints` (Mathlib's `{x | IsClosed {x}}`) using `Homeomorph.subtype`. The membership condition holds because a homeomorphism maps closed sets to closed sets (`isClosed_image`). So, as a construction, it is correct.

But the only thing it uses about the scheme isomorphism is its underlying homeomorphism. No sheaf, scheme or algebraic structure is involved. The same construction works word for word for any homeomorphism `X ≃ₜ Y` between topological spaces: closedness of singletons is a purely topological property, and it is preserved under homeomorphisms. The natural generality is therefore "a homeomorphism of topological spaces restricts to a homeomorphism of closed-point subspaces". `closedPoints` itself is defined in Mathlib at that topological generality (`Mathlib/Topology/JacobsonSpace.lean`).

The scheme version would be the topological construction applied to `e.schemeIsoToHomeo`. As written, it ties a purely topological statement to schemes for no reason. Mathlib has no general `Homeomorph`-on-`closedPoints` declaration, so I give no counterpart. Its general tool is `Homeomorph.subtype`, which the definition applies directly.

### [`MvPolynomial.localizedCoordinateInverseBase`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/LocalizedCoordinateQuotient.lean#L131-L134) — `formal-frontier-0961`

Snippet: `samples/formal-frontier/formal-frontier-0961.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ValuationRing.localizedPowerImage`](https://github.com/FormalFrontier/adic-modules/blob/6f6fa8b3b08a9dba6faa90e328c8d528645f7d5b/AdicModules/LocalizedFiltration.lean#L39-L42) — `formal-frontier-0966`

Snippet: `samples/formal-frontier/formal-frontier-0966.lean`

- **verdict**: `too_narrow`
- **intended_object**: The image of the base-ring ideal (a)^n = a^n·V in a localization V_S, viewed as a V-submodule of V_S, i.e. {a^n v / 1 : v ∈ V}. It is not the extended ideal a^n·V_S. Inferred from the docstring and the module documentation.
- **mathlib_counterpart**: Submodule.map
- **explanation**: The body is `Submodule.map (Algebra.linearMap V Vₛ) ((Ideal.span {a}) ^ n)`. This is the V-submodule of Vₛ made of the images of the elements of a^n·V, so it matches the docstring.

The construction needs nothing from the surrounding hypotheses. It works for any commutative (semi)ring V, any V-algebra Vₛ and any ideal I in place of (a); in Mathlib terms it is just `Submodule.map` of `I ^ n` along `Algebra.linearMap`.

- **Not included at all:** the body never mentions `S`, so neither `S` nor `[IsLocalization S Vₛ]` is pulled into the definition. The definition is therefore not even tied to a localization.
- **Included but unused:** `[IsDomain V]` and `[ValuationRing V]` are pulled in because `V` appears. The body never uses them.

The valuation-ring hypothesis matters only for the later lemmas: total divisibility gives the sandwich (a)^{n+1}V_S ⊆ image ⊆ (a)^n V_S. The definition itself does not need it. It is therefore stated more narrowly than its natural generality, which is an arbitrary commutative ring (or at least an arbitrary localization) and an arbitrary ideal or element.

It could also be read as an auxiliary device for the filtration comparison. Taken as a mathematical object, though, it is a standard image submodule, artificially restricted to valuation domains.

