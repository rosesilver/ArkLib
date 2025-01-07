/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Composition.Basic

/-!
  # The Fiat-Shamir Transformation

  This file defines the Fiat-Shamir transformation. This transformation takes in a (public-coin)
  interactive reduction (IR) `R` and transforms it into a non-interactive reduction via removing
  interaction from `R`. In particular, in the transformed reduction, queries to the verifier's
  challenges are replaced by queries to a random oracle.

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  There are many variants of Fiat-Shamir. The most theoretical one is that one hashes the entire
  statement and transcript up to the point of deriving a new challenge. This is inefficient and not
  actually how it is implemented in practice.

  In contrast, most implementations today use the hash function as a **cryptographic sponge**, which
  permits adding in bitstrings (serialized from the messages) and squeezing out new bitstrings (that
  are then de-serialized into challenges).
-/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

-- def FSOracleSpec (pSpec : ProtocolSpec n) : OracleSpec (ι ++ ℕ) :=

/-- TODO: change `unifSpec` to something more appropriate (maybe a `CryptographicSponge`) -/
def FiatShamirTransform (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    NonInteractiveReduction (oSpec ++ₒ unifSpec) StmtIn WitIn StmtOut WitOut
      (∀ i, pSpec.Message i) :=
  sorry
