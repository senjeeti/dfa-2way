import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card


-- Create a generic variable for the alphabet type, and for the state type
variable {σ : Type}

-- Define words/language over alphabet σ
@[reducible]
def word (σ : Type) := List σ
@[reducible]
def language (σ : Type) := Set (word σ)
def pow {σ : _} (l : word σ) : Nat → word σ
  | 0  => []
  | n+1  => l ++ pow l n

-- Define the set of alphabet
structure DFA (S : Finset σ) where
  q : Type -- Define a generic state type within the DFA structure
  Q : Finset q
  δ : q → σ → q
  q₀ : q
  F : Finset q
  [d₁ : DecidableEq σ]
  [d₂ : DecidableEq q]

-- Let D be a DFA with alphabet S (consisting of σ)
variable {S: Finset σ} {D : DFA S}

-- Define the δ* function
-- the state reached after following all transitions given a word
-- the first letter in list is the last character consumed
@[simp]
def δ_star' (q : D.Q) : (w : word S) → D.Q
  | [] => q
  | e :: es => δ_star' (D.δ q e) es

def δ_star : (w : word S) → D.Q := δ_star' D.q₀ w
