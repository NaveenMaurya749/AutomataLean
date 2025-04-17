import AutomataLean.Basic
import Mathlib

universe u v w

open Computability

/-
# Determinstic Finite Automaton (DFA)
DFAs are theretical models of computation that accept "regular languages".
Mathematicaly, a DFA is a 5-tuple (Q, Σ, δ, q0, F) where
-- Q is a finite set of states
-- Σ is a finite set of input symbols,
-- δ : Q × Σ → Q is the transition function,
-- q0 ∈ Q is the initial state,
-- and F ⊆ Q is the set of accepting states.

This has already been implemented in Mathlib.Computability.DFA
-/

/-
structure DFA.{u, v} (α : Type u) (σ : Type v) : Type (max u v)
number of parameters: 2
fields:
  DFA.step : σ → α → σ
  DFA.start : σ
  DFA.accept : Set σ
constructor:
  DFA.mk.{u, v} {α : Type u} {σ : Type v} (step : σ → α → σ) (start : σ) (accept : Set σ) : DFA α σ
-/
#print DFA

/-
structure NFA.{u, v} (α : Type u) (σ : Type v) : Type (max u v)
number of parameters: 2
fields:
  NFA.step : σ → α → Set σ
  NFA.start : Set σ
  NFA.accept : Set σ
constructor:
  NFA.mk.{u, v} {α : Type u} {σ : Type v} (step : σ → α → Set σ) (start accept : Set σ) : NFA α σ
-/
#print NFA

/-
structure εNFA.{u, v} (α : Type u) (σ : Type v) : Type (max u v)
number of parameters: 2
fields:
  εNFA.step : σ → Option α → Set σ
  εNFA.start : Set σ
  εNFA.accept : Set σ
constructor:
  εNFA.mk.{u, v} {α : Type u} {σ : Type v} (step : σ → Option α → Set σ) (start accept : Set σ) : εNFA α σ
-/
#print εNFA

/-
# Pushdown Automata (PDA)
PDAs are a more powerful model of computation than DFAs, as they can accept "context-free languages".
Mathematicaly, a PDA is a 6-tuple (Q, Σ, Γ, δ, q0, F) where
-- Q is a finite set of states
-- Σ is a finite set of input symbols,
-- Γ is a finite set of stack symbols,
-- δ : Q × Σ × Γ → Set (Q × Γ*) is the transition function,
-- q0 ∈ Q is the initial state,
-- and F ⊆ Q is the set of accepting states.
-/

structure PDA (Q : Type u) (α : Type v) (Γ : Type w) where
  /-- A transition function from state to state labelled by the alphabet. -/
  transition : Q → Option α → Γ → Q × (List Γ)
  inital_state : Q
  initial_stack : Γ
  accept : Q → Prop

#do_later "Worry about Fintype and Finite later"

namespace PDA

variable {Q : Type u} {α : Type v} {Γ : Type w} (M : PDA Q α Γ)

-- Inhabited instance for PDA
instance [Inhabited Q] [Inhabited Γ]: Inhabited (PDA Q α Γ) :=
    ⟨PDA.mk (fun _ _ _ => default) (default) (default) (fun _ => default)⟩

structure InstantDesc (M : PDA Q α Γ) where
  state : Q
  input_tape : List α
  stack_tape : List Γ

/-Example of DFA-/
def my_dfa : DFA Char Bool :=
  { step := (fun q _ => ¬ q)
    start := 0
    accept := fun q => q = true}

#eval my_dfa.eval "sdas".toList

-- Example of a PDA that accepts the language of balanced parentheses.

--namespace Balanced

inductive Parentheses : Type
| left | right
deriving Inhabited, Repr

inductive States : Type
| q0 | q1 | q2
deriving Inhabited, Repr, Fintype

inductive Stack : Type
| A | Z
deriving Inhabited, Repr

open Parentheses States Stack

def my_pda : PDA States Parentheses Stack :=
  ⟨(fun q x y =>
    match q, x, y with
    | q0, some left,  Z => (q0, [A, Z])
    | q0, some left,  A => (q0, [A, A])
    | q1, none,       Z => (q1, [Z])
    | q1, none,       A => (q1, [A])
    | q1, some right, A => (q1, [])
    | q2, none,       Z => (q2, [Z])
    | _, _, _           => (q2, [])
    ),
    q0,
    Z,
    (fun y => y = q0)
  ⟩
#note "Yayyyyyyyyyyyy!!!!!!!!!!!!!"

-- end Balanced

#check PDA.transition

def evalStep (M : PDA Q α Γ) (desc : InstantDesc M) : InstantDesc M :=
  have ⟨q, input, stack⟩ := desc
  match input, stack with
  | _, [] => ⟨q, input, stack⟩
  | [], top::rest =>
    let (q', new_stack) := M.transition q none top
    ⟨q', [], new_stack ++ rest⟩
  | x::xs, top::rest =>
    let (q', new_stack) := M.transition q (some x) top
    ⟨q', xs, new_stack ++ rest⟩

/-[@simp]
theorem evalStep_blank (M : PDA Q α Γ) (desc : InstantDesc M) : M.evalStep desc = desc := by
  simp [evalStep]
  split
  · sim
  · simp
  · sorry

-/

lemma evalStep_decrements_input (desc : InstantDesc M) (hi : desc.input_tape ≠ []) (hs : desc.stack_tape ≠ []) :
  (M.evalStep desc).input_tape.length < desc.input_tape.length := by
    match desc with
    | ⟨q, _, []⟩ => contradiction
    | ⟨_, _, top::rest⟩ =>
      simp only [List.length_cons]
      unfold evalStep
      simp
      split
      · simp
      · simp

#do_later "Add [@simp] lemmas"

def evalFrom (M : PDA Q α Γ) (desc : InstantDesc M) : Q :=
  match desc with
  | ⟨q, _, []⟩ => q
  | ⟨_, _, _⟩ =>
    evalFrom M (evalStep M desc)
termination_by desc.input_tape.length
decreasing_by
  sorry
  -- simp [evalStep]
  -- split
  -- todo "Prove this terminates"
  -- -- sorry

def eval (M : PDA Q α Γ) (input : List α) : Q :=
  M.evalFrom ⟨M.inital_state, input, [M.initial_stack]⟩

def accepts (M : PDA Q α Γ) (input : List α) : Prop :=
  M.accept (M.eval input)

/-
failed to synthesize
  Decidable (my_pda.accepts [left, right, left, right])

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
set_option diagnostics true
#eval my_pda.accepts [left, right, left, right]
