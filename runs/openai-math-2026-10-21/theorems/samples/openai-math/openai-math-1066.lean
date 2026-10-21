namespace OAI

namespace KS.W01.MagnitudeProgram

open KS.W29

open KS.W03.MachineCombinators

open KS.W01.BinaryAdder

theorem runSpec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool)
    (store : Fin k → List Bool) (xs : List Bool)
    (hzero : store (ports 0) = []) (hpayload : store (ports 1) = xs)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports carry) store
      (Function.update store (ports 1) (result carry xs)) (2 * xs.length + 3) :=
  (runSpec ports carry store xs hzero hpayload hscratch).mono (ticks_le carry xs)

end KS.W01.MagnitudeProgram
end OAI
