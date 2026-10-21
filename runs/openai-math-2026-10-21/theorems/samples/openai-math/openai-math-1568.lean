namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic

open WordOperations WordList BinaryArithmetic

open BinaryOpeningPayment (field field_computes field_encode)

lemma counts_pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) :
    counts (pack b d ps raw)=NaturalArray.encode (ps.map (fun p=>⌊p*(2:ℚ)^b⌋₊)) := by
  simp only [counts,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    scale_replicate,RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,count_pack,NaturalArray.encode]

end MetricKMedianRecovery.BitMachine.BinaryDyadic
end OAI
