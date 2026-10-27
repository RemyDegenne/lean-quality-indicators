public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A nonnegative resolution whose terms are acyclic for `Ext X -` in
positive degrees. -/
structure AcyclicResolution (X A : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ n, cocomplex.HasHomology n]
  ι : (CochainComplex.single₀ C).obj A ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance
  extAcyclic : ∀ n q, 0 < q → Subsingleton (Ext X (cocomplex.X n) q)

end CategoryTheory.Abelian.Ext
end
end
