import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
namespace P2MW.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq

open WeierstrassCurve

theorem solution {K : Type*} [Field K] [DecidableEq K]
    {X Y : WeierstrassCurve K} {E : WeierstrassCurve.VariableChange K} (h : E • X = Y) :
    Y.card = X.card :=
  Nat.card_congr (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h)
