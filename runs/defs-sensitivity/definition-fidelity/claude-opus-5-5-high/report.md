# definition-fidelity: run `defs-sensitivity`, judge `claude-opus-5-5-high`

| Library | Sampled | Judged | `not_a_mathematical_object` | `unclear` | Assessed | Flagged | `incorrect` | `too_narrow` | `no_docstring` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0.0% | 0.0%–79.3% | $0.04 |
| Tau Ceti | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0.0% | 0.0%–79.3% | $0.14 |
| Lean Pool | 7 | 7 | 0 | 0 | 7 | 5 | 0 | 5 | 0 | 71.4% | 35.9%–91.8% | $0.58 |
| Formal Frontier | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0.0% | 0.0%–79.3% | $0.02 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (0 flagged)


## Tau Ceti (0 flagged)


## Lean Pool (5 flagged)

### [`LeanPool.HansonWright.frobeniusNorm`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/HansonWright/Probability/Concentration/HansonWright.lean#L205-L207) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Frobenius (Hilbert–Schmidt) norm of a matrix, ‖A‖_F = (∑_{i,j} |a_ij|²)^{1/2}. This comes from the docstring and the name.
- **mathlib_counterpart**: Matrix.frobeniusNormedAddCommGroup
- **explanation**: The body is sqrt(∑ i, ∑ j, (A i j)^2), which is exactly the Frobenius norm, so the formula is correct, including for n = 0. However, it is defined only for square real matrices indexed by Fin n. The construction needs only finitely many rows and columns and a norm on the entries. It makes sense for rectangular m×n matrices with any finite index types and entries in any normed (additive) group, such as ℝ or ℂ. Squareness, the Fin n indexing and the choice of ℝ come from how the Hanson–Wright development uses it, not from the definition. Mathlib provides this norm in that generality: the local instance Matrix.frobeniusNormedAddCommGroup (and the seminormed version Matrix.frobeniusSeminormedAddCommGroup) on Matrix m n α, with Matrix.frobenius_norm_def stating ‖A‖ = (∑ i, ∑ j, ‖A i j‖^2)^(1/2). The library's definition is therefore a special-case rewrite of a general Mathlib norm.

### [`AVenhance.Infra.Parabolic.FourierGalerkin.vecDot`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/ODE.lean#L49-L50) — `lean-pool-0001`

Snippet: `samples/lean-pool/lean-pool-0001.lean`

- **verdict**: `too_narrow`
- **intended_object**: The standard dot product ⟨u, v⟩ = Σ_k u_k v_k of two vectors, taken here on ℝ² (vectors `Fin 2 → ℝ`). This comes from the docstring ("ordinary dot product on `Vec 2`") and the name.
- **mathlib_counterpart**: dotProduct
- **explanation**: The body `∑ k, u k * v k` is the correct dot product, so the definition is right for ℝ². But it is a copy of Mathlib's `dotProduct` (Mathlib/Data/Matrix/Mul.lean), which is defined as `∑ i, v i * w i` for any finite index type `m` and any `[Mul α] [AddCommMonoid α]`. Nothing in the body depends on the index type being `Fin 2` or on the scalars being ℝ; it only needs finitely many indices and a sum of products. The docstring explains why it was written out locally (to avoid importing the library's PDE definitions), but that is about module dependencies, not about the mathematics. The 2D setting is not needed for the construction, and `vecDot u v` is definitionally `dotProduct u v` (written `u ⬝ᵥ v`). So it is a special case of a general Mathlib construction, written out by hand: too narrow.

### [`VML.normSq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Clawristotle/Defs.lean#L35-L36) — `lean-pool-0002`

Snippet: `samples/lean-pool/lean-pool-0002.lean`

- **verdict**: `too_narrow`
- **intended_object**: The squared Euclidean norm ‖z‖² = z·z = ∑ᵢ zᵢ² of a vector z (from the docstring). Here it is stated only for vectors in ℝ³, the velocity space of the Vlasov–Maxwell–Landau system.
- **mathlib_counterpart**: dotProduct
- **explanation**: The body is `dotProduct z z` for `z : Fin 3 → ℝ`, which is ∑ᵢ zᵢ². So the value is correct: it is exactly the squared Euclidean norm of z. Nothing in the construction needs dimension 3, and the lemmas proved right after it (nonnegativity, `= 0 ↔ z = 0`, positivity, invariance under negation) hold for any `Fin n → ℝ`, and more generally for any finite index type over a linear ordered ring. The squared Euclidean norm is a standard notion on ℝⁿ and on any real inner product space. Mathlib already covers it in general: the root-level `dotProduct v w` for `v w : m → α` with `m` a fintype, which here is applied to the pair (z, z), and `‖x‖ ^ 2 = ⟪x, x⟫` on `EuclideanSpace ℝ n` and other inner product spaces. So the definition re-implements a general Mathlib construction in one fixed dimension. The rubric lists exactly this case (a notion on ℝᵈ that makes sense in general) as too narrow. The library works in 3 dimensions because the physics is 3D, but this particular definition does not depend on that.

### [`EllipticPdes.Classical.laplacianSum`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EllipticPDE/Existence/Harmonic.lean#L50-L52) — `lean-pool-0003`

Snippet: `samples/lean-pool/lean-pool-0003.lean`

- **verdict**: `too_narrow`
- **intended_object**: The Laplacian Δu(x) = Σ_i ∂²u/∂x_i²(x) of a real-valued function on ℝ^d. This comes from the docstring ("sum of the second coordinate partials") and from how the library uses it: harmonic, subharmonic and superharmonic conditions and maximum principles in Existence/Harmonic.lean.
- **mathlib_counterpart**: InnerProductSpace.instLaplacian
- **explanation**: The body computes Σ_i (fderiv (y ↦ fderiv u y e_i) x) e_i on `EuclideanSpace ℝ (Fin d)`, with `partialD i φ x = fderiv ℝ φ x (single i 1)`. Wherever u is twice differentiable this is the usual Laplacian.

Where u is not twice differentiable, the value can differ from Mathlib's Δ, which gives 0 when the outer `fderiv` fails to exist. Since `partialD` is itself built on `fderiv`, it also returns 0 at points where u has a partial derivative but no Fréchet derivative. Both differences are only about junk values, so the definition is mathematically correct.

The problem is generality. Mathlib already defines the Laplacian (`Δ`, via `InnerProductSpace.instLaplacian` in Mathlib/Analysis/InnerProductSpace/Laplacian.lean) for functions E → F, where E is any finite-dimensional real inner product space and F any normed space. Mathlib also proves the sum-of-second-derivatives formula for any orthonormal basis (`laplacian_eq_iteratedFDeriv_orthonormalBasis`). The Laplacian does not depend on coordinates: the coordinate sum is the same for every orthonormal basis. So the only properties of ℝ^d used here are an inner product and finite dimension; the restriction to `EuclideanSpace ℝ (Fin d)` and to real values is not needed. This is a case of writing out, in one particular setting, a construction Mathlib provides in general.

### [`NRR.EMP.weightMean`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/EMP/WeightSpace.lean#L59-L61) — `lean-pool-0005`

Snippet: `samples/lean-pool/lean-pool-0005.lean`

- **verdict**: `too_narrow`
- **intended_object**: The arithmetic mean (1/n)·∑ᵢ wᵢ of a finite vector (w₁,…,wₙ). This comes from the docstring and the module documentation, where the mean is used to normalize weight vectors to sum zero.
- **mathlib_counterpart**: Finset.expect
- **explanation**: The definition is mathematically correct. It is `(∑ i, w i) / n` for `w : Fin n → ℝ`, which is the arithmetic mean. In the degenerate case n = 0 it gives 0/0 = 0, which matches Mathlib's convention (`Finset.expect_empty`).

The body uses nothing particular to `Fin n` or to `ℝ`. It only needs a finite index set and division of a sum by a natural number. Mathlib already provides this construction in full generality as `Finset.expect` (notation `𝔼 i, f i`): any finset of any index type, valued in any `AddCommMonoid` with a `Module ℚ≥0` structure. By `Finset.expect_univ`, `𝔼 i, w i = (∑ i, w i) /ℚ Fintype.card ι`, and that is exactly `weightMean w` when ι = Fin n and the values are in ℝ.

So the definition writes out, in one particular setting (real vectors indexed by `Fin n`), an averaging operator that Mathlib defines generally. Nothing in its content needs that setting, so it is too narrow rather than faithful.


## Formal Frontier (0 flagged)

