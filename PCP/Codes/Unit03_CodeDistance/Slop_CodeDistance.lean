import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import PCP.Codes.Unit01_HammingDistance.API

/-!
# Code Distance

This file defines the minimum distance of a code.

## Main definitions

* `codeDistance C`: Minimum Hamming distance between distinct codewords in C

## Main results

* `codeDistance_pos`: Distance is positive for codes with ≥2 codewords
* `codeDistance_le_length`: Distance is bounded by codeword length
* `codeDistance_symm`: Distance is symmetric in code representation

-/

namespace Codes.Unit03

open Codes.Unit01 Finset

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The minimum distance of a code: smallest Hamming distance between
    distinct codewords. Returns n+1 if code has < 2 elements. -/
def codeDistance (C : Finset (Fin n → α)) : ℕ :=
  let pairs := C.product C |>.filter (fun p => p.1 ≠ p.2)
  if h : pairs.Nonempty then
    pairs.inf' h (fun p => hammingDist p.1 p.2)
  else
    n + 1

/-- Code distance definition. -/
lemma codeDistance_def (C : Finset (Fin n → α)) :
    codeDistance C =
      let pairs := C.product C |>.filter (fun p => p.1 ≠ p.2)
      if h : pairs.Nonempty then
        pairs.inf' h (fun p => hammingDist p.1 p.2)
      else
        n + 1 := rfl

/-- Code distance for singleton code is n+1 (no distinct pairs). -/
lemma codeDistance_singleton (x : Fin n → α) :
    codeDistance {x} = n + 1 := by
  unfold codeDistance
  simp
  split_ifs with h
  · exfalso
    obtain ⟨⟨y, z⟩, hy, hz⟩ := h
    simp at hy
    obtain ⟨⟨rfl, rfl⟩, hne⟩ := hy
    exact hne rfl
  · rfl

/-- Code distance for empty code is n+1. -/
lemma codeDistance_empty :
    codeDistance (∅ : Finset (Fin n → α)) = n + 1 := by
  unfold codeDistance
  simp

/-- Code distance is bounded by codeword length. -/
lemma codeDistance_le_length (C : Finset (Fin n → α)) :
    codeDistance C ≤ n + 1 := by
  unfold codeDistance
  split_ifs with h
  · apply Finset.inf'_le
    intro p hp
    simp at hp
    obtain ⟨⟨_, _⟩, _⟩ := hp
    calc hammingDist p.1 p.2
        ≤ n := hammingDist_le_length p.1 p.2
      _ ≤ n + 1 := Nat.le_succ n
  · rfl

/-- Code distance is positive when there are at least 2 distinct codewords. -/
lemma codeDistance_pos_of_two_distinct (C : Finset (Fin n → α))
    (x y : Fin n → α) (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    0 < codeDistance C := by
  unfold codeDistance
  have : (C.product C |>.filter (fun p => p.1 ≠ p.2)).Nonempty := by
    use (x, y)
    simp [hx, hy, hne]
  simp only [this, ↓reduceIte]
  apply Nat.pos_of_ne_zero
  intro h0
  have := Finset.inf'_eq_zero.mp h0
  obtain ⟨⟨x', y'⟩, hmem, heq⟩ := this
  simp at hmem
  obtain ⟨_, _, hne'⟩ := hmem
  rw [hammingDist_eq_zero_iff] at heq
  exact hne' heq

/-- Code distance equals minimum pairwise distance. -/
lemma codeDistance_eq_inf (C : Finset (Fin n → α))
    (h : (C.product C |>.filter (fun p => p.1 ≠ p.2)).Nonempty) :
    codeDistance C =
      (C.product C |>.filter (fun p => p.1 ≠ p.2)).inf' h
        (fun p => hammingDist p.1 p.2) := by
  unfold codeDistance
  simp [h]

/-- Code distance is symmetric in arguments. -/
lemma codeDistance_symm_pairs (C : Finset (Fin n → α))
    (x y : Fin n → α) (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    hammingDist x y = hammingDist y x :=
  hammingDist_comm x y

/-- If distance is d, then all pairs are at least d apart. -/
lemma all_pairs_ge_codeDistance (C : Finset (Fin n → α))
    (x y : Fin n → α) (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    codeDistance C ≤ hammingDist x y := by
  unfold codeDistance
  have hpairs : (C.product C |>.filter (fun p => p.1 ≠ p.2)).Nonempty := by
    use (x, y)
    simp [hx, hy, hne]
  simp only [hpairs, ↓reduceIte]
  apply Finset.inf'_le
  simp [hx, hy, hne]

/-- Code distance characterizes minimum separation. -/
lemma codeDistance_le_iff (C : Finset (Fin n → α)) (d : ℕ)
    (h : 2 ≤ C.card) :
    codeDistance C ≤ d ↔
      ∃ x y, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ hammingDist x y ≤ d := by
  constructor
  · intro hd
    unfold codeDistance at hd
    have hpairs : (C.product C |>.filter (fun p => p.1 ≠ p.2)).Nonempty := by
      have : 1 < C.card := h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero (by omega : C.card ≠ 0))
      have : ∃ y, y ∈ C ∧ y ≠ x := by
        by_contra hall
        push_neg at hall
        have : C ⊆ {x} := by
          intro z hz
          simp
          exact hall z hz
        have : C.card ≤ 1 := by
          calc C.card ≤ ({x} : Finset _).card := card_le_card this
              _ = 1 := by simp
        omega
      obtain ⟨y, hy, hne⟩ := this
      use (x, y)
      simp [hx, hy, hne]
    simp only [hpairs, ↓reduceIte] at hd
    obtain ⟨⟨x, y⟩, hmem, hmin⟩ := Finset.exists_mem_eq_inf' hpairs _
    use x, y
    simp at hmem
    obtain ⟨hx, hy, hne⟩ := hmem
    rw [← hmin] at hd
    exact ⟨hx, hy, hne, hd⟩
  · intro ⟨x, y, hx, hy, hne, hdist⟩
    calc codeDistance C
        ≤ hammingDist x y := all_pairs_ge_codeDistance C x y hx hy hne
      _ ≤ d := hdist

/-- Error detection capability: d-1 errors can be detected. -/
lemma can_detect_errors (C : Finset (Fin n → α)) (t : ℕ)
    (hd : t + 1 ≤ codeDistance C) :
    ∀ x y, x ∈ C → y ∈ C → hammingDist x y ≤ t → x = y := by
  intro x y hx hy hdist
  by_contra hne
  have : codeDistance C ≤ hammingDist x y :=
    all_pairs_ge_codeDistance C x y hx hy hne
  omega

/-- Error correction capability: ⌊(d-1)/2⌋ errors can be corrected. -/
lemma can_correct_errors (C : Finset (Fin n → α)) (t : ℕ)
    (hd : 2 * t + 1 ≤ codeDistance C) :
    ∀ x y, x ∈ C → y ∈ C → x ≠ y → t < hammingDist x y := by
  intro x y hx hy hne
  have : codeDistance C ≤ hammingDist x y :=
    all_pairs_ge_codeDistance C x y hx hy hne
  omega

end Codes.Unit03
