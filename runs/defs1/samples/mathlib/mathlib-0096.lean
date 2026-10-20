namespace Pentagonal

open Filter

open scoped Topology

variable {R : Type*} [CommRing R]

/--
We define an auxiliary sequence

$$ a_{k, n} = x^{(k+1)n} \prod_{i=0}^{n} (1 - x^{k + i + 1}) $$

We will also use its sum

$$ A_k = \sum_{n=0}^{\infty} a_{k, n} $$ -/
def powMulProdOneSubPow (k n : ℕ) (x : R) : R :=
  x ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - x ^ (k + i + 1))

end Pentagonal
