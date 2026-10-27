@[expose] public section

open Function

universe u v

namespace ProfiniteGrp

/-- The continuous primewise map determined by an element of a profinite
group. -/
noncomputable def primewisePadicMapOfGenerator (G : ProfiniteGrp.{u}) (g : G) :
    primewisePadic.{u} →ₜ* G :=
  (integerCompletionMap G g).hom.comp
    (integerCompletionEquivPrimewisePadic.{u}.symm :
      primewisePadic.{u} →ₜ* integerCompletion.{u})

end ProfiniteGrp
end
