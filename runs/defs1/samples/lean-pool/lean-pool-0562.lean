@[expose] public section

namespace LO

namespace Modal

namespace Kripke

open Formula.Kripke

infix:80 " ⇄ " => Model.Bisimulation

infix:50 " ↭ " => ModalEquivalent

infix:80 " →ₚ " => Frame.PseudoEpimorphism

infix:80 " →ₚ " => Model.PseudoEpimorphism

section «lp_section_4»

infix:100 "↾" => Frame.PointGenerated

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.PointGenerated (M : Kripke.Model) (r : M.World) :
    Kripke.RootedModel :=
  letI rF := M.toFrame↾r;
  {
    toFrame := rF.toFrame
    Val := fun w a => M.Val w.1 a
    root := rF |>.root
    root_rooted := rF.root_rooted
  }

end «lp_section_4»
end Kripke
end Modal
end LO
end
