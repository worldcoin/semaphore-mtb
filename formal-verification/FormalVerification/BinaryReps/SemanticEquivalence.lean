import FormalVerification
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence_Aux
import FormalVerification.Keccak.SemanticEquivalence
import ProvenZk.Gates

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

theorem reduced
