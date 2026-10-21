namespace OAI

namespace TuringRigidity.AutomorphismUnion

open Set PersistentRestrictions CountableForcing

theorem value_graph (G : GenericFilter Approximation) (a : Domain G) :
    Graph G a.val (value G a).val := Classical.choose_spec (graph_total G a.property)

end TuringRigidity.AutomorphismUnion
end OAI
