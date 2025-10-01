/-
  Language Encodings

  Bitstring encodings, input representations, SAT language definition

  Difficulty: ★☆☆☆☆ (1/5)
  Estimated LOC: 80
  Work Package: WP-A
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/-!
# Language Encodings

Bitstring encodings, input representations, SAT language definition

Based on the PCP theorem formalization plan following Dinur's gap amplification approach.
-/

/-- A bitstring is a finite sequence of bits (booleans). -/
abbrev Bitstring := List Bool

/-- A language is a set of bitstrings. -/
abbrev Language := Set Bitstring

namespace Bitstring

/-- Concatenation of bitstrings. -/
def concat (x y : Bitstring) : Bitstring := x ++ y

/-- The empty bitstring. -/
def empty : Bitstring := []

end Bitstring

namespace Language

/-- The empty language. -/
def empty : Language := ∅

/-- The universal language (all bitstrings). -/
def univ : Language := Set.univ

end Language
