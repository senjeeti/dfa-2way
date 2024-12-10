-- Project members: Sanjna Enjeeti, Krish Suraparaju
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
    simp [List.count, Nat.mod_zero]
    trivial
  | cons a input ih =>
    cases Nat.decEq a 0 with
    | isTrue h =>

      rw [h]
      rw [List.count_cons]
      have even_flip : ∀ n, (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 := by
        intro n
        simp [Nat.add_mod, Nat.mod_eq_of_lt]
        cases Nat.mod_two_eq_zero_or_one n with
        | inl h => simp [h]
        | inr h => simp [h]
      simp
      rw [even_flip]
      rw [DFA.accepts, DFA.runDFA]
      rw [List.foldl_cons]
      simp [List.count_cons]
      sorry
    | isFalse h =>  -- case where a ≠ 0
      rw [List.count_cons]
      simp [Nat.add_mod]
      simp
      rw [if_neg h]
      simp [Nat.add_zero, Nat.mod_eq_of_lt]
      have step1 : evenZeroDFA.accepts (a :: input) = evenZeroDFA.accepts input := by {
        rw [DFA.accepts]
        have state_preservation : ∀ (s : String),
          DFA.runDFA evenZeroDFA (a :: input) = DFA.runDFA evenZeroDFA (input) := by {
          rw [DFA.runDFA]
          simp [evenZeroDFA, if_neg h]
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

inductive Direction where
  | Left : Direction
  | Right : Direction
deriving DecidableEq

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

   let rec run_helper (config : Configuration Q A) (steps : Nat) : Option Q :=
    if steps = 0 then
      some config.state
    else if config.state = dfa.qaccept ∨ config.state = dfa.qreject then
      some config.state
    else
      match dfa.step config with
      | none => none  -- Invalid configuration
      | some next_config => run_helper next_config (steps - 1)

  run_helper init_config n

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

def evenZeroTwoWayDFA {Q A} [DecidableEq Q] [Nonempty Q] [Nonempty A] : TwoWayDFA String Nat :=
  TwoWayDFA.mkTwoWayDFA

    (Multiset.toFinset ["q0", "q1", "qaccept", "qreject"])

    (Multiset.toFinset [0,1])

    (λ q a =>
      match q, a with

      | q, Sum.inr true => ("q0", Direction.Right)  -- Always move right on left endmarker


      | "q0", Sum.inr false => ("qaccept", Direction.Left)  -- Even zeros - accept
      | "q1", Sum.inr false => ("qreject", Direction.Left)  -- Odd zeros - reject


      | "q0", Sum.inl 0 => ("q1", Direction.Right)  -- Even to odd
      | "q0", Sum.inl 1 => ("q0", Direction.Right)  -- Stay even
      | "q1", Sum.inl 0 => ("q0", Direction.Right)  -- Odd to even
      | "q1", Sum.inl 1 => ("q1", Direction.Right)  -- Stay odd


      | "qaccept", _ => ("qaccept", Direction.Right)
      | "qreject", _ => ("qreject", Direction.Right)

      -- Default case
      | _, _ => ("qreject", Direction.Right))
    -- Initial state
    "q0"
    -- Accept state
    "qaccept"
    -- Reject state
    "qreject"

    (λ q a => by
      unfold ValidTransition

      cases a with
      | inr b =>
        cases b with
        | true =>
          simp [Direction.Right]
        | false =>
          simp [Direction.Left]
          sorry
      | inl x =>

        by_cases h : q = "qaccept" ∨ q = "qreject"
        . simp [h, Direction.Right]
          match q with
          | "qaccept" => simp [h]
          | "qreject" => simp [h]
          | _ =>
            cases h with
            | inl hq => sorry  -- Because q isn't qaccept
            | inr hq => sorry
        . simp [h]
        )

theorem evenZeroTwoWayDFA_correct :
  ∀ (input : List ℕ),
  TwoWayDFA.accepts (@evenZeroTwoWayDFA String ℕ _ _ _) input "qaccept" "qreject" =
  ((input.count 0) % 2 = 0) := by

  intro input

  induction input with
  | nil =>
    -- Base case: empty list
    dsimp [TwoWayDFA.accepts, TwoWayDFA.run, evenZeroTwoWayDFA]
    simp [List.count, Nat.mod_zero]
    sorry

  | cons head tail ih =>

    by_cases h : head = 0

    .
      rw [h]
      simp [List.count]
      -- Adding a zero flips the parity
      have parity_flip : ∀ n, (n + 1) % 2 = 0 ↔ n % 2 = 1 := by
        intro n
        cases n % 2 with
        | zero =>
          -- If n % 2 = 0, then (n + 1) % 2 = 1
          simp [Nat.add_mod]
          simp
          sorry
        | succ k =>
          -- If n % 2 = 1, then (n + 1) % 2 = 0
          cases k with
          | zero =>
            simp [Nat.add_mod]
            simp
            sorry
          | succ k' =>
            simp
            sorry


      sorry

    .
      simp [List.count, h]

      sorry



end TwoWayDFA_Impl

open DFA_Impl TwoWayDFA_Impl

inductive AugmentedState (Q : Type)
| Original : Q → AugmentedState Q
| Accept : AugmentedState Q
| Reject : AugmentedState Q
deriving DecidableEq

/- Helper function to convert a 2-way DFA into a DFA -/
def twoway_to_dfa {Q A} [DecidableEq Q] [Nonempty Q] [Nonempty A]
                 (twoway: TwoWayDFA Q A) : DFA Q A :=

  let states' := twoway.states
  let sigma' := twoway.sigma
  let delta' := (λ q a =>

      let (after_left, _) := twoway.delta q (Sum.inr true)

      let (next_state, _) := twoway.delta after_left (Sum.inl a)

      let (final_state, _) := twoway.delta next_state (Sum.inr false)

      if final_state = twoway.qaccept then twoway.qaccept
      else if final_state = twoway.qreject then twoway.qreject
      else next_state)
  let q0' := twoway.q₀
  let accept_states := Finset.mk {twoway.qaccept} (by simp [Multiset.nodup_singleton])
  DFA.mkDFA states' sigma' delta' q0' accept_states



theorem twoway_to_dfa_accept {Q A} [DecidableEq Q] [Nonempty Q] [Nonempty A] (twoway: TwoWayDFA Q A) :
  ∀ (input : List A),
    -- (which means it can be done in a single left-to-right pass)
    DFA.accepts (twoway_to_dfa twoway) input ↔
    TwoWayDFA.accepts twoway input twoway.qaccept twoway.qreject := by

  let dfa := twoway_to_dfa twoway

  intro input

  let dfa_accepts := dfa.accepts input
  let twoway_accepts := twoway.accepts input twoway.qaccept twoway.qreject

  -- Unfold the definitions
  unfold DFA.accepts at dfa_accepts
  unfold TwoWayDFA.accepts at twoway_accepts

  -- Show that running the DFA leads to an accepting state
  -- if and only if the 2-way DFA reaches qaccept
  have h_final_state : DFA.runDFA dfa input =
    TwoWayDFA.run twoway input input.length := by
    -- Induction on the input list
    induction input with
    | nil =>
      -- Base case: empty input
      simp [DFA.runDFA, TwoWayDFA.run]
      -- Both machines start at their initial states
      have h_start : dfa.q₀ = twoway.q₀ := by rfl

      rw [h_start]
      let left_trans := twoway.delta twoway.q₀ (Sum.inr true)
      let right_trans := twoway.delta left_trans.1 (Sum.inr false)
      if h : right_trans.1 = twoway.qaccept then

        sorry
      else if h : right_trans.1 = twoway.qreject then
        sorry
      else
        have h_running : right_trans.1 ≠ twoway.qaccept ∧ right_trans.1 ≠ twoway.qreject := ⟨by assumption, by assumption⟩
        sorry
    | cons head tail ih =>
      -- Inductive case: head :: tail
      simp [DFA.runDFA, TwoWayDFA.run]
      -- Show that processing one more symbol preserves equivalence
      -- Use the inductive hypothesis ih
      have h_tail := ih
      simp [DFA.runDFA, TwoWayDFA.run] at h_tail

      sorry

  -- Show that accepting states correspond
  have h_accept_equiv :
    ∀ q : Q, q = twoway.qaccept → q ∈ dfa.F := by
    intro q
    intro h
    rw [h]

    -- The DFA's accepting states are exactly twoway.qaccept
    sorry

  -- Combine the lemmas to prove equivalence
  sorry


-- /- Helper function to convert a DFA into a 2-way DFA -/
-- def dfa_to_2dfa {Q A} [DecidableEq Q] [Nonempty Q] [Nonempty A]
--                 (dfa: DFA Q A) : TwoWayDFA Q A :=
--   -- Convert DFA states and add accept/reject states
--   let qaccept := AugmentedState dfa.accepts
--   let states' := insert qaccept dfa.states
--   -- Create transition function that always moves right and simulates DFA
--   let delta' (q: Q) (a: TapeAlphabet A) : Q × Direction :=
--     match a with
--     | Sum.inr true => (dfa.q₀, Direction.Right)  -- Left endmarker: move right to start
--     | Sum.inr false =>  -- Right endmarker: accept if in accepting state
--         if q ∈ dfa.F
--         then ("qaccept", Direction.Left)
--         else ("qreject", Direction.Left)
--     | Sum.inl sym =>  -- Regular symbol: simulate DFA transition
--         (dfa.delta q sym, Direction.Right)

--   TwoWayDFA.mkTwoWayDFA
--     states'
--     dfa.sigma
--     delta'
--     dfa.q₀
--     "qaccept"
--     "qreject"
--     (by
--       -- Prove transition function validity
--       intro q a
--       unfold ValidTransition
--       cases a with
--       | inr b =>
--         cases b with
--         | true => simp [Direction.Right]  -- Left endmarker moves right
--         | false => simp [Direction.Left]  -- Right endmarker moves left
--       | inl x =>
--         by_cases h : q = "qaccept" ∨ q = "qreject"
--         . simp [h, Direction.Right]
--         . simp [h])


-- /- Main equivalence theorem -/
-- theorem dfa_2dfa_equiv {Q A} [DecidableEq Q] [Nonempty Q] [Nonempty A] :
--   ∀ (L : Set (List A)),
--   (∃ dfa: DFA Q A, ∀ w, w ∈ L ↔ dfa.accepts w) ↔
--   (∃ twoway: TwoWayDFA Q A, ∀ w, w ∈ L ↔
--     TwoWayDFA.accepts twoway w twoway.qaccept twoway.qreject) := by

--   intro L
--   constructor

--   -- Forward direction: DFA → 2-way DFA
--   { intro h
--     rcases h with ⟨dfa, h⟩
--     -- Convert DFA to 2-way DFA using our helper function
--     let twoway := dfa_to_2dfa dfa
--     existsi twoway

--     -- Show that the languages recognized are equivalent
--     intro w
--     -- Main argument: 2-way DFA simulates DFA by moving right
--     have sim_step : ∀ (pos : Nat) (state : Q),
--       pos ≤ w.length →
--       -- Each step of 2-way DFA matches DFA state
--       sorry

--     -- Use simulation to prove equivalence
--     sorry }

--   -- Reverse direction: 2-way DFA → DFA
--   { intro h
--     rcases h with ⟨twoway, h⟩
--     -- Convert 2-way DFA to DFA using helper function
--     let dfa := twoway_to_dfa twoway
--     existsi dfa

--     -- Show languages are equivalent
--     intro w
--     -- Main argument: DFA can track all possible configurations
--     have config_bound : ∀ (steps : Nat),
--       steps ≤ w.length * twoway.states.card →
--       -- DFA state encodes valid 2-way DFA configuration
--       sorry

--     -- Use configuration tracking to prove equivalence
--     sorry }
