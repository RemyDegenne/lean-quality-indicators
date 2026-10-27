@[expose] public section

namespace CategoryTheory.Limits

universe t w w' v u

namespace MulticospanIndex

variable {C : Type u} [Category.{v} C] {J : MulticospanShape.{w, w'}}
  (I : MulticospanIndex J C)

/-- The multicospan associated to `I : MulticospanIndex`. -/
def multicospan : WalkingMulticospan J ⥤ C where
  obj x :=
    match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

end MulticospanIndex
end CategoryTheory.Limits
end
