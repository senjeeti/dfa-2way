-- Project members: Krish Suraparaju, Sanjna Enjeeti
-- Project description: We will implement a deterministic finite automaton (DFA) in Lean 4.
-- This consists of defining the DFA structure, and functions to run the DFA on some input
-- and check if the DFA accepts the input, or not. We will also come up with some toy
-- examples of DFAs and prove their correctness (or attempt to).

import Mathlib.Data.Finset.Basic


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

-- First define the direction the head can move
inductive Direction where
  | Left : Direction
  | Right : Direction
deriving DecidableEq

-- For a given alphabet A, we extend it with endmarkers
def TapeAlphabet (A : Type) := A ⊕ Bool
-- Left endmarker is (Sum.inr true)
-- Right endmarker is (Sum.inr false)
-- Regular symbols are (Sum.inl a) for a : A

-- Define a 2-way DFA as a structure with seven fields:
-- Q - Finite, nonempty set of states
-- A - Finite, nonempty set of alphabet symbols
-- δ : Q × (A ⊕ Bool) → Q × Direction - Transition function
-- q₀ ∈ Q - Start state
-- qaccept ∈ Q - Accepting state
-- qreject ∈ Q - Rejecting state
structure TwoWayDFA
  (Q : Type) [DecidableEq Q] [Nonempty Q]
  (A : Type) [Nonempty A] where
  states : Finset Q
  sigma : Finset A
  delta : Q → TapeAlphabet A → Q × Direction
  q₀ : Q
  qaccept : Q
  qreject : Q


-- Define when a transition function is valid:
-- 1. Must move right on left endmarker
-- 2. Must move left on right endmarker
-- 3. Accept/reject states must move right on non-endmarker symbols
def ValidTransition {Q A} [DecidableEq Q] (q : Q) (a : TapeAlphabet A)
                         (delta : Q → TapeAlphabet A → Q × Direction)
                         (qaccept : Q) (qreject : Q) : Prop :=

  match a with
  | Sum.inr true => (delta q a).2 = Direction.Right    -- Left endmarker case
  | Sum.inr false => (delta q a).2 = Direction.Left    -- Right endmarker case
  | Sum.inl _ =>
  if q = qaccept ∨ q = qreject
  then (delta q a).2 = Direction.Right
  else true

-- Construct a 2-way DFA from given parameters
def TwoWayDFA.mkTwoWayDFA {Q} [DecidableEq Q] [Nonempty Q]
                          {A} [Nonempty A]
                          (states: Finset Q)
                          (sigma: Finset A)
                          (delta: Q → TapeAlphabet A → Q × Direction)
                          (q₀: Q)
                          (qaccept: Q)
                          (qreject: Q)
                          (h: ∀ q a, ValidTransition q a delta qaccept qreject) : TwoWayDFA Q A :=
  { states := states
  , sigma := sigma
  , delta := delta
  , q₀ := q₀
  , qaccept := qaccept
  , qreject := qreject }



-- Configuration represents the current state of computation
structure Configuration (Q A : Type) where
  state : Q
  input : List (TapeAlphabet A)
  position : Nat

-- Step function computes the next configuration if possible
def TwoWayDFA.step {Q} [DecidableEq Q] [Nonempty Q]
                   {A} [Nonempty A]
                   (dfa : TwoWayDFA Q A)
                   (config : Configuration Q A) : Option (Configuration Q A) :=
  match config.input.get? config.position with
  | none => none  -- Invalid position
  | some symbol =>
      let (next_state, dir) := dfa.delta config.state symbol
      some ⟨next_state,
            config.input,
            match dir with
            | Direction.Left =>
                if config.position = 0
                then 0
                else config.position - 1
            | Direction.Right =>
                min (config.position + 1) (config.input.length - 1)⟩

-- Run the 2-way DFA for n steps
def TwoWayDFA.run {Q} [DecidableEq Q] [Nonempty Q]
                  {A} [Nonempty A]
                  (dfa : TwoWayDFA Q A)
                  (input : List A)
                  (n : Nat) : Option Q :=
  let init_config := Configuration.mk
    dfa.q₀
    ((Sum.inr true) :: (input.map Sum.inl) ++ [Sum.inr false])
    0
  sorry

-- A 2-way DFA accepts if it reaches the accepting state
def TwoWayDFA.accepts {Q} [DecidableEq Q] [Nonempty Q]
                      {A} [Nonempty A]
                      (dfa : TwoWayDFA Q A)
                      (input : List A)
                      (qaccept : Q) (qreject : Q): Bool :=
  -- A configuration is accepting if we reach accept state within bounds
  -- Run until we either accept or detect a loop
  -- NOTE: temporary number inserted in place of # of total states for the sake of termination
  let max_steps := input.length * 100000000
  let rec try_steps (n : Nat) (seen : Finset (Q) ) (left : ℕ): Bool :=
    -- Get the state after n steps
    let (state_option) := dfa.run input n
    -- If we've reached either terminal state, return the result
    match state_option with
    | some state => if state ∈ seen then false else
                    if left = 0 then false else
                    if state = qaccept then true
                    else if state = qreject then false
                    else try_steps (n + 1) (insert state seen) (left - 1)
    | none => false

  -- Start trying from 0 steps
  try_steps 0 ∅ max_steps



end TwoWayDFA_Impl

-- namespace TwoWayDFA_Impl

-- -- First, let's define the direction the head can move
-- inductive Direction
-- | Left : Direction  -- Move left (-1)
-- | Right : Direction -- Move right (+1)

-- -- We'll create a type for our tape alphabet which includes the endmarkers
-- structure TapeAlphabet (S : Type) :=
-- (symbols : S)                    -- The input alphabet
-- (left_end : S)                   -- Left endmarker ⊢
-- (right_end : S)                  -- Right endmarker ⊣

-- -- Now we'll define the structure of a 2-way DFA
-- structure TwoWayDFA (Q S : Type) :=
-- (states : Q)                     -- Set of states
-- (alphabet : TapeAlphabet S)      -- Tape alphabet (including endmarkers)
-- (initial : Q)                    -- Initial state
-- (accept : Q)                     -- Accepting state
-- (reject : Q)                     -- Rejecting state
-- (transition : Q × S → Q × Direction)  -- Transition function δ

-- -- Let's define the constraints on the transition function
-- def valid_transition {Q S : Type} (M : TwoWayDFA Q S) : Prop :=
-- -- For all states x, when reading left_end, must move right
-- ∀ x : Q, (M.transition (x, M.alphabet.left_end)).2 = Direction.Right ∧
-- -- For all states x, when reading right_end, must move left
-- ∀ x : Q, (M.transition (x, M.alphabet.right_end)).2 = Direction.Left ∧
-- -- For accepting and rejecting states, must move right on non-endmarker symbols
-- ∀ σ : S, σ ≠ M.alphabet.left_end → σ ≠ M.alphabet.right_end →
--   (M.transition (M.accept, σ)).2 = Direction.Right ∧
--   (M.transition (M.reject, σ)).2 = Direction.Right

-- -- A configuration represents the current state of computation
-- structure Configuration (Q S : Type) :=
-- (state : Q)           -- Current state
-- (input : List S)      -- Input string (including endmarkers)
-- (position : ℕ)        -- Current head position (0-based index)

-- -- Step function computes the next configuration
-- def step {Q S : Type} (M : TwoWayDFA Q S) (c : Configuration Q S) : Configuration Q S :=
-- let (next_state, dir) := M.transition (c.state, c.input.nth c.position) in
-- Configuration.mk
--   next_state
--   c.input
--   (match dir with
--    | Direction.Left => c.position - 1
--    | Direction.Right => c.position + 1)

-- -- Define when a computation accepts
-- def accepts {Q S : Type} (M : TwoWayDFA Q S) (input : List S) : Prop :=
-- ∃ (n : ℕ),
--   let init_config := Configuration.mk M.initial (M.alphabet.left_end :: input ++ [M.alphabet.right_end]) 0 in
--   (iterate n (step M) init_config).state = M.accept

-- -- Define when a computation rejects
-- def rejects {Q S : Type} (M : TwoWayDFA Q S) (input : List S) : Prop :=
-- ∃ (n : ℕ),
--   let init_config := Configuration.mk M.initial (M.alphabet.left_end :: input ++ [M.alphabet.right_end]) 0 in
--   (iterate n (step M) init_config).state = M.reject

-- end TwoWayDFA_Impl


-- Extension to the Project:
-- Consider the 2DFA, which is a DFA that can move its head to the
-- left or right on the input list. We can extend the DFA structure
-- to include the tape head position, and the transition function
-- can be modified to move the head left or right based on the input.
-- It has been shown that 2DFAs are equivalent to DFAs, so as a final
-- extension, we can try to prove this equivalence in Lean 4.
-- namespace TwoWayDFA_Impl
-- -- Define a 2DFA as a structure with six fields:
-- -- Q, Σ, δ, q0, F, and head.
-- -- Q - Finite, nonempty set of states
-- -- A - Finite, nonempty set of alphabet symbols
-- -- δ : Q × Σ → Q × {L, R} - Transition function
-- -- q₀ ∈ Q - Start state
-- -- F ⊆ Q - Set of accepting states
-- -- head ∈ Z - Tape head position
-- inductive Direction where
--   | L
--   | R

-- tructure DFA (α : Type u) (σ : Type v) :=
-- (step : σ → α → σ)
-- (start : σ)
-- (accept : set σ)

-- structure TwoWayDFA
--   (Q : Type) [DecidableEq Q] [Nonempty Q]
--   (A : Type) [Nonempty A] where
--   states : Finset Q
--   sigma : Finset A
--   delta : Q → A → Q × Direction
--   q₀ : Q
--   F : Finset Q
--   head : Int -- index of the tape head

-- -- Constructs a 2DFA from the given parameters.
-- def TwoWayDFA.mk2DFA {Q} [DecidableEq Q] [Nonempty Q]
--           {A} [Nonempty A]
--           (states: Finset Q)
--           (sigma: Finset A)
--           (delta: Q → A → Q × Direction)
--           (q₀: Q)
--           (F: Finset Q)
--           (head: Int) : TwoWayDFA Q A :=
--     { states := states
--     , sigma := sigma
--     , delta := delta
--     , q₀ := q₀
--     , F := F
--     , head := head }

-- -- Given a 2DFA and an input string, this function
-- -- returns the final state after processing the input.
-- -- The input string is represented as a list of symbols.
-- structure Configuration (Q : Type) where
--   state : Q
--   head : Int
--   deriving DecidableEq

-- -- theorem get_index_spec {α} (as : List α) (i : Nat) :
-- --   as.get? i = Option.map (λ h => as.get ⟨i, h⟩) (Nat.decLt i as.length) := by
-- --   cases Nat.decLt i as.length with
-- --   | isFalse h => simp [List.get?, h]
-- --   | isTrue h => simp [List.get?, h]

-- /-- Get a symbol from the input tape at a given position.
--     Returns None if the position is out of bounds. -/
-- def getInputSymbol {A} (input : List A) (pos : Int) : Option A :=
--   if h : 0 ≤ pos ∧ pos < input.length then
--     -- Convert Int position to Nat for list access
--     have h_nat : pos.toNat < input.length := by
--       cases pos with
--       | ofNat n => simp [Int.toNat] at *; exact h.2
--       | negSucc n => simp [Int.toNat] at *
--     some (input.get ⟨pos.toNat, h_nat⟩)
--   else
--     none

-- def TwoWayDFA.step {Q} [DecidableEq Q] [Nonempty Q]
--            {A} [Nonempty A]
--            (dfa: TwoWayDFA Q A)
--            (input: List A)
--            (config: Configuration Q) : Option (Configuration Q) :=
--   match getInputSymbol input config.head with
--   | none => none  -- Head has moved out of bounds
--   | some symbol =>
--       let (newState, dir) := dfa.delta config.state symbol
--       let newHead := config.head + match dir with
--                                  | Direction.L => -1
--                                  | Direction.R => 1
--       some ⟨newState, newHead⟩

-- def TwoWayDFA.run2DFA {Q} [DecidableEq Q] [Nonempty Q]
--            {A} [Nonempty A]
--            (dfa: TwoWayDFA Q A)
--            (input: List A) : Q :=
--   let initialConfig := ⟨dfa.q₀, dfa.head⟩
--   let rec run (config: Configuration Q) (fuel: Nat) : Q :=
--     match fuel, dfa.step input config with
--     | 0, _ => config.state  -- Out of fuel, return current state
--     | fuel'+1, none => config.state  -- Invalid move, return current state
--     | fuel'+1, some nextConfig =>
--         -- Continue only if we haven't seen this configuration before
--         if nextConfig.head < 0 ∨ nextConfig.head ≥ input.length
--         then config.state  -- Return current state if head moves out of bounds
--         else run nextConfig fuel'

--   -- This is a conservative bound as we might visit each position in each state
--   -- num_states is a parameter
--   run initialConfig (input.length * input.length)

-- def TwoWayDFA.accepts {Q} [DecidableEq Q] [Nonempty Q]
--                     {A} [Nonempty A]
--                     (dfa : TwoWayDFA Q A)
--                     (input : List A) : Bool := by
--   let finalState := TwoWayDFA.run2DFA dfa input dfa.states.card
--   finalState ∈ dfa.F




-- end TwoWayDFA_Impl
-- open DFA_Impl
-- open TwoWayDFA_Impl
-- theorem dfa_to_2dfa_equivalence {Q} [DecidableEq Q] [Nonempty Q]
--                              {A} [Nonempty A]
--                              (dfa : DFA Q A)
--                              (input : List A) :
--   DFA.accepts dfa input = TwoWayDFA.accepts (DFA_to_2DFA dfa) input := by
-- begin
--   -- Prove that the DFA and the constructed 2DFA accept the same input strings
--   induction input with
--   | nil =>
--     -- Base case: empty input
--     simp [DFA.accepts, DFA.runDFA, TwoWayDFA.accepts, TwoWayDFA.run2DFA, DFA_to_2DFA]
--     rfl
--   | cons a input ih =>
--     -- Inductive case: non-empty input
--     simp [DFA.accepts, DFA.runDFA, TwoWayDFA.accepts, TwoWayDFA.run2DFA, DFA_to_2DFA]
--     rw [ih]
--     simp [DFA_to_2DFA, TwoWayDFA.step]
--     -- Show that the DFA and 2DFA state transitions are the same
--     have state_eq : DFA.runDFA dfa input = TwoWayDFA.run2DFA (DFA_to_2DFA dfa) input := by
--       rw [DFA.runDFA, TwoWayDFA.run2DFA, DFA_to_2DFA]
--       induction input with
--       | nil => simp
--       | cons b input' ih =>
--         simp [DFA.runDFA, TwoWayDFA.run2DFA, DFA_to_2DFA]
--         rw [ih]
--         simp [DFA_to_2DFA, TwoWayDFA.step]
--     rw [state_eq]
--     -- Show that the final states are in the accepting set iff
--     -- the original DFA and the constructed 2DFA both accept
--     cases mem_of_eq_of_mem (DFA.runDFA dfa input) (TwoWayDFA.run2DFA (DFA_to_2DFA dfa) input) dfa.F with
--     | inl h => exact h
--     | inr h => exact h
-- end
