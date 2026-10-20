public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

namespace AcyclicResolution

variable {X A : C} (R : AcyclicResolution X A)

variable {B : C} (R' : AcyclicResolution X B)

variable {R'}

/-- Iterating the canonical dimension shifts moves Ext of degree-`n` cycles
back to Ext of the degree-zero cycles. -/
@[expose] noncomputable def cyclesDimensionShiftIterate :
    (n q : ℕ) → 0 < q → Ext X (R.cocomplex.cycles n) q ≃+
      Ext X (R.cocomplex.cycles 0) (n + q)
  | 0, q, _ => AddEquiv.cast (by omega)
  | n + 1, q, hq =>
      (R.cyclesDimensionShift n q hq).trans
        ((cyclesDimensionShiftIterate n (q + 1) (by omega)).trans
          (AddEquiv.cast (by omega)))

end AcyclicResolution
end CategoryTheory.Abelian.Ext
end
end
