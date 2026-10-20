@[expose] public section

open Function

universe u v

namespace ProfiniteGrp

theorem primewisePadicKernelIdeal_mapOfGenerator_eq
    (G : ProfiniteGrp.{u}) (g h : G)
    (hg : IsTopologicalGenerator G g) (hh : IsTopologicalGenerator G h) :
    primewisePadicKernelIdeal (primewisePadicMapOfGenerator G g) =
      primewisePadicKernelIdeal (primewisePadicMapOfGenerator G h) :=
  primewisePadicKernelIdeal_eq_of_surjective
    (primewisePadicMapOfGenerator G g) (primewisePadicMapOfGenerator G h)
    (primewisePadicMapOfGenerator_surjective G g hg)
    (primewisePadicMapOfGenerator_surjective G h hh)

end ProfiniteGrp
end
