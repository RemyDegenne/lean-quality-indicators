@[expose] public section

namespace AtanasovRanganathan.GenusFourGeneratedRows.G4Row100

open Utilities

open MarkedGraphs.Certificate

open Utilities.Certificate

open Utilities.Certificate.ContractionForestCensusGeneral

open Utilities.Subdivision.ClosedRowProof

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw3 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0,
          -1], [0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(0, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], 1, 1⟩,
          ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [],
          0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)],
      [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [],
      0⟩, ⟨1, [(8, 1)], [], 0⟩] }

end AtanasovRanganathan.GenusFourGeneratedRows.G4Row100
end
