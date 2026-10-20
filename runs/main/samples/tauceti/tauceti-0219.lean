public section

open CategoryTheory Abelian

universe w v u

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

namespace H

include hS

theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

end H
end Sheaf
end CategoryTheory
end
