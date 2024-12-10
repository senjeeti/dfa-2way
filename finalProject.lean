-- Project members: Krish Suraparaju, Sanjna Enjeeti
-- Project description: We will implement a deterministic finite automaton (DFA) in Lean 4.
-- This consists of defining the DFA structure, and functions to run the DFA on some input
-- and check if the DFA accepts the input, or not. We will also come up with some toy
-- examples of DFAs and prove their correctness (or attempt to).

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace DFA_Impl
-- Define a DFA  as a structure with five
-- fields: Q, Σ, δ, q0, and F.
-- Q - Finite, nonempty set of states
-- A - Finite, nonempty set of alphabet symbols
-- δ : Q × Σ → Q - Transition function
-- q₀ ∈ Q - Start state
-- F ⊆ Q - Set of accepting states
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
    { states := states
    , sigma := sigma
    , delta := delta
    , q₀ := q₀
    , F := F }

-- Given a DFA and an input string, this function
-- returns the final state after processing the input.
-- The input string is represented as a list of symbols.
def DFA.runDFA {Q} [DecidableEq Q] [Nonempty Q]
           {A} [Nonempty A]
           (dfa: DFA Q A)
           (input: List A) : Q :=
  input.foldl dfa.delta dfa.q₀


-- Given a DFA and an input string, this function
-- returns true if the DFA accepts the input string,
-- and false otherwise.
def DFA.accepts {Q} [DecidableEq Q] [Nonempty Q]
            {A} [Nonempty A]
            (dfa: DFA Q A)
            (input: List A) : Bool :=
  (dfa.runDFA input) ∈ dfa.F



-- USAGE EXAMPLES
-- DFA that accepts strings with an even number of zeros.
def evenZeroDFA : DFA String Nat :=
  DFA.mkDFA (Multiset.toFinset ["q0", "q1"])
        (Multiset.toFinset [0, 1])
        (λ q a =>
          match q, a with
          | "q0", 0 => "q0"
          | "q0", 1 => "q1"
          | "q1", 0 => "q1"
          | "q1", 1 => "q0"
          | _, _ => "q0")
         "q0"
        (Multiset.toFinset ["q0"])


-- Prove correctness of the evenZeroDFA.
theorem evenZeroDFA_correct (input: List Nat) :
  evenZeroDFA.accepts input = ((input.count 0) % 2 = 0) := by
  induction input with
  | nil =>
    dsimp [DFA.accepts, DFA.runDFA, evenZeroDFA]
    simp [List.count, Nat.mod_zero]  -- `List.count 0 [] = 0`
    trivial
  | cons a input ih =>
    cases Nat.decEq a 0 with
    | isTrue h =>  -- case where a = 0

      rw [h]  -- substitute a with 0
      rw [List.count_cons]  -- expand List.count for (0 :: input)
      have even_flip : ∀ n, (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 := by
        intro n
        simp [Nat.add_mod, Nat.mod_eq_of_lt]
        cases Nat.mod_two_eq_zero_or_one n with
        | inl h => simp [h]
        | inr h => simp [h]
      simp
      rw [even_flip]
      rw [DFA.accepts, DFA.runDFA] -- Expand DFA behavior
      rw [List.foldl_cons]
      simp [List.count_cons]
      sorry
    | isFalse h =>  -- case where a ≠ 0
      rw [List.count_cons]  -- expand `count 0 (a :: input')`
      simp [Nat.add_mod]    -- simplify modular arithmetic
      simp
      rw [if_neg h]  -- Simplify the if-then-else since we know a ≠ 0
      simp [Nat.add_zero, Nat.mod_eq_of_lt]  -- Simplify addition with zero and modulo
      have step1 : evenZeroDFA.accepts (a :: input) = evenZeroDFA.accepts input := by {
        rw [DFA.accepts]
        have state_preservation : ∀ (s : String),
          DFA.runDFA evenZeroDFA (a :: input) = DFA.runDFA evenZeroDFA (input) := by {
          rw [DFA.runDFA]  -- Expand the DFA execution
          simp [evenZeroDFA, if_neg h]  -- Simplify using a ≠ 0
          rw [DFA.runDFA, evenZeroDFA] at *
          simp [if_neg h] at *
          sorry
        }
        rw [state_preservation "q0"]
        trivial
      }
      rw [step1, ih]
end DFA_Impl

namespace TwoWayDFA_Impl

-- We start by defining directions
inductive Direction where
  | Left : Direction
  | Right : Direction
deriving DecidableEq

-- For a given alphabet A, the tape alphabet includes A plus two special booleans for endmarkers.
def TapeAlphabet (A : Type) := A ⊕ Bool

-- Special symbols for endmarkers
def LE {A} : TapeAlphabet A := Sum.inr true
def RE {A} : TapeAlphabet A := Sum.inr false

-- A 2DFA structure as described:
structure TwoWayDFA
  (Q : Type) [DecidableEq Q] [Nonempty Q]
  (A : Type) [Nonempty A] where
  states : Finset Q
  sigma : Finset A
  delta : Q → TapeAlphabet A → Q × Direction
  q₀ : Q
  qaccept : Q
  qreject : Q

namespace TwoWayDFA -- O1 CODE BELOW

variables {Q A : Type} [DecidableEq Q] [Nonempty Q] [Nonempty A]

-- Well-formedness conditions capturing the requirements:
-- For all states q, δ(q, LE) moves right and δ(q, RE) moves left.
-- For all b in Σ ∪ {LE}, δ(t, b) = (t, R) and δ(r, b) = (r, R).
-- For δ(t, RE) = (t, L) and δ(r, RE) = (r, L).
def WellFormed (M : TwoWayDFA Q A) : Prop :=
  (∀ q, (M.delta q LE).snd = Direction.Right) ∧
  (∀ q, (M.delta q RE).snd = Direction.Left) ∧
  (∀ b, (b = LE ∨ ∃ a : A, b = Sum.inl a) →
    M.delta M.qaccept b = (M.qaccept, Direction.Right) ∧
    M.delta M.qreject b = (M.qreject, Direction.Right)) ∧
  (M.delta M.qaccept RE = (M.qaccept, Direction.Left) ∧
   M.delta M.qreject RE = (M.qreject, Direction.Left))

-- Extend the input x with endmarkers: x : List A
def extendInput (x : List A) : List (TapeAlphabet A) :=
  LE :: (x.map Sum.inl) ++ [RE]

-- A configuration is a pair (q, i) with q in Q and i indexing into [0..(n+1)]
structure Configuration (Q A : Type) [DecidableEq Q] [Nonempty Q] [Nonempty A] where
  q : Q
  i : Nat

-- The one-step transition relation (1−→ₓ):
-- (p, i) 1−→ₓ (q, j) if δ(p, tape[i]) = (q, D) and j = i+1 if D=R, j = i-1 if D=L
def stepRel (M : TwoWayDFA Q A) (x : List A) (c1 c2 : Configuration Q A) : Prop :=
  let tape := extendInput x
  if c1.i < tape.length ∧ c2.i < tape.length then
    match tape.get? c1.i with
    | none => False
    | some sym =>
      let (q', dir) := M.delta c1.q sym
      c2.q = q' ∧
      (dir = Direction.Right ∧ c2.i = c1.i + 1 ∨ dir = Direction.Left ∧ c2.i = c1.i - 1)
  else
    False

-- Define n−→ₓ by induction on n
inductive nStepRel (M : TwoWayDFA Q A) (x : List A) : Nat → Configuration Q A → Configuration Q A → Prop
| zero {c} : nStepRel M x 0 c c
| succ {c1 c2 c3 n} :
    nStepRel M x n c1 c2 → stepRel M x c2 c3 →
    nStepRel M x (n+1) c1 c3

-- The *−→ₓ relation: (p, i)*−→ₓ(q, j) if ∃ n, (p, i) n−→ₓ (q, j)
def starRel (M : TwoWayDFA Q A) (x : List A) (c1 c2 : Configuration Q A) : Prop :=
  ∃ n, nStepRel M x n c1 c2

-- Acceptance: M accepts x if (s,0)*−→ₓ(qaccept, i) for some i
def accepts (M : TwoWayDFA Q A) (x : List A) : Prop :=
  let tape := extendInput x
  ∃ i < tape.length, starRel M x ⟨M.q₀, 0⟩ ⟨M.qaccept, i⟩

-- Rejection: M rejects x if (s,0)*−→ₓ(qreject, i) for some i
def rejects (M : TwoWayDFA Q A) (x : List A) : Prop :=
  let tape := extendInput x
  ∃ i < tape.length, starRel M x ⟨M.q₀, 0⟩ ⟨M.qreject, i⟩

-- The language L(M) accepted by M:
def L (M : TwoWayDFA Q A) : Set (List A) := { x | M.accepts x }

-- M loops on x if it neither accepts nor rejects x.
def loops (M : TwoWayDFA Q A) (x : List A) : Prop :=
  ¬ M.accepts x ∧ ¬ M.rejects x

-- Extended structure with well-formedness and distinctness conditions
structure TwoWayDFAWithWF
  (Q : Type) [DecidableEq Q] [Nonempty Q]
  (A : Type) [Nonempty A] extends TwoWayDFA Q A where
  h_wf : TwoWayDFA.WellFormed toTwoWayDFA
  h_distinct : qreject ≠ qaccept

-- Now we define the 'run' function.
-- The run function attempts to simulate the machine:
-- It returns:
--   Some true if M accepts x
--   Some false if M rejects x
--   None if it loops on x
def run (M : TwoWayDFAWithWF Q A) (x : List A) : Option Bool :=
  let tape := extendInput x

  -- Because Q is finite and tape length is finite, we can detect loops by checking
  -- whether a configuration repeats.
  let rec loop (visited : Finset (Q × Nat)) (c : Configuration Q A) : Option Bool :=
    if c.q = M.qaccept then
      -- Accept
      some true
    else if c.q = M.qreject then
      -- Reject
      some false
    else if (c.q, c.i) ∈ visited then
      -- We've seen this configuration before -> loop detected
      none
    else
      match tape.get? c.i with
      | none =>
        -- This should not happen if c.i is in range.
        none
      | some sym =>
        let (q', dir) := M.delta c.q sym
        let i' := if dir = Direction.Right then c.i + 1 else c.i - 1
        if h : i' < tape.length then
          loop (visited ∪ {(c.q, c.i)}) { q := q', i := i' }
        else
          -- Should not occur in a well-formed 2DFA, but we handle it gracefully.
          none
  -- Provide a termination measure:
  -- Each recursive call adds a new configuration to visited, so visited.card increases.
  -- Thus N - visited.card decreases strictly.
  termination_by (M.states.card * tape.length) - visited.card
  decreasing_by
    -- In each recursive call, we do `visited ∪ (c.q, c.i)`.
    -- The cardinality of visited after insertion is visited.card + 1 if (c.q, c.i) was not already in visited.
    -- Thus N - visited.card decreases by 1.
    apply Nat.lt_of_le_of_lt (Nat.le_refl _)
    -- In previous calls visited.card < N because once visited.card = N we would have covered all configurations.
    -- Thus visited.card < N.

    sorry -- For a full proof, you'd show that the number of visited configurations is always strictly less than N before recursion.

  loop ∅ {q := M.q₀, i := 0}


end TwoWayDFA
