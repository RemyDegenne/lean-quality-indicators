@[expose] public section

open CategoryTheory Convexity

namespace TopCat

universe w

variable {X Y : TopCat.{w}} (p : Y ⟶ X)

/-- Restrict a lift of a singular simplex along an arbitrary simplex operator. -/
noncomputable def singularLiftRestrict {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l)
    (s : (toSSet.obj X).obj k) :
    {u : (toSSet.obj Y).obj k // (toSSet.map p).app k u = s} →
      {u : (toSSet.obj Y).obj l //
        (toSSet.map p).app l u = (toSSet.obj X).map α s} :=
  fun u => ⟨(toSSet.obj Y).map α u.val, by
    change (toSSet.obj X).map α ((toSSet.map p).app k u.val) = _
    exact congrArg ((toSSet.obj X).map α) u.property⟩

end TopCat
end
