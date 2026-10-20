@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

theorem powerImage_not_isSheafFor_root (n : ℕ) (hn : 2 ≤ n) :
    ¬ Presieve.IsSheafFor ((powerImage K n).toFunctor)
      (Presieve.singleton (powerRootMap K n (laurentTest K) (laurentUnit K)).op) := by
  apply subfunctor_not_isSheafFor_singleton_of_injective
    (powerImage K n) (powerRootMap K n (laurentTest K) (laurentUnit K)).op
    (laurentUnit K)
  · exact powerRootMap_mem_powerImage K n (laurentTest K) (laurentUnit K)
      (by omega)
  · change Function.Injective
      (Units.map (powerRootMap K n (laurentTest K) (laurentUnit K)).hom.hom.toMonoidHom)
    exact Units.map_injective
      ((powerRootMap_faithfullyFlat K n (laurentTest K) (laurentUnit K)
        (by omega)).injective)
  · exact laurentUnit_not_mem_powerImage K n hn

end AlgebraicGeometry
end
