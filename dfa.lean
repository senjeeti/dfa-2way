-- Project members: Sanjna Enjeeti, Krish Suraparaju
-- Project description: We will implement a deterministic finite automaton (DFA) in Lean 4.
-- This consists of defining the DFA structure, and functions to run the DFA on some input
-- and check if the DFA accepts the input, or not. We will also come up with some toy
-- examples of DFAs and prove their correctness (or attempt to).

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Init.Set

-- First, define what a word and a language are.

@[reducible]
def word : Type _ := List A

@[reducible]
def Language : Type _ := Set (word A)

def star {Sigma : _} (l : word A) : Nat → word A
  | 0  => []
  | n+1  => l ++ star l n



-- Define DFA
namespace DFA_Impl
-- Define a DFA  as a structure with five
-- fields: Q, Σ, δ, q0, and F.
-- Q - Finite, nonempty set of states
-- A - Finite, nonempty set of alphabet symbols
-- δ : Q × Σ → Q - Transition function
-- q₀ ∈ Q - Start state
-- F ⊆ Q - Set of accepting states

def deterministicDelta {Q} [DecidableEq Q] [Nonempty Q]
  {A} [Nonempty A]
  (delta : Q → A → Q) : Prop :=
  ∀ (q : Q) (a : A), ∃! (q' : Q), delta q a = q'

structure DFA
  (Q : Type) [DecidableEq Q] [Nonempty Q]
  (A : Type) [Nonempty A] where
  states : Finset Q
  sigma : Finset A
  delta : Q → A → Q
  q₀ : Q
  F : Finset Q


-- Constructs a DFA from the given parameters.
def DFA.mkDFA {Q} [DecidableEq Q] [Nonempty Q]
          {A} [Nonempty A]
          (states: Finset Q)
          (sigma: Finset A)
          (delta: Q → A → Q)
          (q₀: Q)
          (F: Finset Q) : DFA Q A :=
  { states := states,
    sigma := sigma,
    delta := delta,
    q₀ := q₀,
    F := F }

-- Given a DFA an input string, and a starting state,
-- this function returns the state that the DFA ends up in
-- after processing the input string from that state
def DFA.runDFA_from {Q} [DecidableEq Q][Nonempty Q]
           {A} [Nonempty A]
           (dfa: DFA Q A)
           (q₀ : Q)
           (input: List A) : Q :=
  List.foldl dfa.delta q₀ input


-- Given a DFA and an input string, this function
-- returns true if the DFA accepts the input string,
-- and false otherwise.
def DFA.accepts {Q} [DecidableEq Q] [Nonempty Q]
            {A} [Nonempty A]
            (dfa: DFA Q A)
            (input: List A) : Bool :=
  (dfa.runDFA_from dfa.q₀ input) ∈ dfa.F


lemma DFA.runDFA_empty {Q} [DecidableEq Q] [Nonempty Q] {A} [Nonempty A]
  (dfa : DFA Q A) (q : Q) :
  dfa.runDFA_from q [] = q := by
    simp [DFA.runDFA_from]
lemma DFA.runDFA_singleton {Q} [DecidableEq Q] [Nonempty Q] {A} [Nonempty A]
  (dfa : DFA Q A) (a : A) (q : Q):
  dfa.runDFA_from q [a] = dfa.delta q a := by
    simp [DFA.runDFA_from]

lemma DFA.runDFA_append {Q} [DecidableEq Q] [Nonempty Q] {A} [Nonempty A]
  (dfa : DFA Q A) (q : Q) (w : List A) (a : A) :
  dfa.runDFA_from q (w ++ [a]) = dfa.delta (dfa.runDFA_from q w) a := by
  simp only [DFA.runDFA_from, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma DFA.runDFA_append' {Q} [DecidableEq Q] [Nonempty Q] {A} [Nonempty A]
  (dfa : DFA Q A) (q : Q) (w1 w2 : List A) :
  dfa.runDFA_from q (w1 ++ w2) = dfa.runDFA_from (dfa.runDFA_from q w1) w2 :=
  w1.foldl_append dfa.delta q w2


-- Prove that the runDFA function produces a unique result
-- given a DFA and an input string. I.E., the DFA is deterministic.
theorem DFA.deterministic {Q} [DecidableEq Q] [Nonempty Q] {A} [Nonempty A]
  (dfa : DFA Q A) :
   ∀ (w : List A), ∃! (q : Q), dfa.runDFA_from dfa.q₀ w = q := by
    intros w
    induction w.length with
    | zero =>
      simp [DFA.runDFA_from]
    | succ _ _ =>
      simp [DFA.runDFA_from]

end DFA_Impl


-- DFA Examples and proofs of correctness

namespace DFA_Examples
open DFA_Impl

-- Example 1: A DFA that accepts strings with an odd number of
-- 'a's in them. The alphabet is {a, b}.
inductive myQ : Type
| q0
| q1
| q2
| q3
deriving DecidableEq, Inhabited

inductive myA : Type
| a
| b
deriving DecidableEq, Inhabited

def odd_DFA : DFA myQ myA :=
  DFA.mkDFA
    {myQ.q0, myQ.q1, myQ.q2, myQ.q3}
    {myA.a, myA.b}
    (λ q c =>
      match q, c with
      | myQ.q0, myA.a => myQ.q3
      | myQ.q0, myA.b => myQ.q1
      | myQ.q1, myA.a => myQ.q2
      | myQ.q1, myA.b => myQ.q0
      | myQ.q2, myA.a => myQ.q1
      | myQ.q2, myA.b => myQ.q3
      | myQ.q3, myA.a => myQ.q0
      | myQ.q3, myA.b => myQ.q2
    )
    myQ.q0
    {myQ.q2}


-- Prove correctness of the odd_DFA
theorem odd_DFA_correct (w : List myA) :
  (odd_DFA.runDFA_from odd_DFA.q₀ w = myQ.q2) ↔
  (List.count myA.a w % 2 = 1 ∧ List.count myA.b w % 2 = 1) := by
  -- Define the strengthened induction hypothesis:
  -- Each state corresponds to specific properties of 'a' and 'b'.
  let stateProps := λ q =>
    match q with
    | myQ.q0 => (List.count myA.a w % 2 = 0 ∧ List.count myA.b w % 2 = 0)
    | myQ.q1 => (List.count myA.a w % 2 = 0 ∧ List.count myA.b w % 2 = 1)
    | myQ.q2 => (List.count myA.a w % 2 = 1 ∧ List.count myA.b w % 2 = 1)
    | myQ.q3 => (List.count myA.a w % 2 = 1 ∧ List.count myA.b w % 2 = 0)

  -- Induction on the length of w
  induction w with
  | nil =>
    -- Base case: w = []
    simp [DFA.runDFA_from, List.foldl, stateProps]
    sorry
  | cons head tail ih =>
    -- Inductive step: w = head :: tail
    cases head with
    | a =>
      simp [DFA.runDFA_from, List.foldl]
      apply stateProps_cons_a; assumption
    | b =>
      simp [DFA.runDFA_from, List.foldl]
      sorry

end DFA_Examples
