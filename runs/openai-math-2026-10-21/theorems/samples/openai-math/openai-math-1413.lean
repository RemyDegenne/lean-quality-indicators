namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma metaplectic_code_ext {r : Eisenstein} {x y : MetaplecticRetainedCode r}
    (hp : metaplecticCodePrefix x = metaplecticCodePrefix y)
    (hw : x.2.2.val = y.2.2.val) : x = y := by
  have hd : x.1 = y.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.1) hp
  have hs : x.2.1 = y.2.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hp
  have hf : x.2.2 = y.2.2 := Subtype.ext hw
  exact Prod.ext hd (Prod.ext hs hf)

end CubicFirstMoment
end
end OAI
