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
  NFA.mk.{u, v} {α : Type u} {σ :success Type v} (step : σ → α → Set σ) (start accept : Set σ) : NFA α σ
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

## Deterministic Pushdown Automata (DPDA)
First, we define a deterministic pushdown automata (DPDA) as a PDA with the following properties:
1. The transition function δ is deterministic, meaning that for each state, input symbol, and stack symbol,
-- there is at most one possible transition.
2. The stack is not allowed to be empty when reading an input symbol.
3. The stack is allowed to be empty when reading an ε-transition.

-/

structure DPDA (Q : Type u) (α : Type v) (Γ : Type w) where
  /-- A transition function from state to state labelled by the alphabet. -/
  transition : Q → Option α → Γ → Option (Q × (List Γ))
  inital_state : Q
  initial_stack : Γ
  accept : Q → Prop
  h_determinism : ∀ (q : Q) (y : Γ),
    transition q none y ≠ none → (a : α) → transition q (some a) y = none

#do_later "Worry about Fintype and Finite later"

namespace DPDA

variable {Q : Type u} {α : Type v} {Γ : Type w} (M : DPDA Q α Γ)

-- Inhabited instance for PDA
instance [Inhabited Q] [Inhabited Γ]: Inhabited (DPDA Q α Γ) :=
    ⟨DPDA.mk (fun _ _ _ => default) (default) (default) (fun _ => default) (fun _ _ _ _ => rfl)⟩

/-
An Instantaneous Description of a PDA is a triple (p, w, β) consists of:
-- p is the current state of the PDA
-- w is the remaining input string
-- β is the current stack contents
The stack contents are represented as a list of symbols, with the top of the stack being the head of the list.
-/

structure InstantDesc (M : DPDA Q α Γ) where
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
| q0 | q1
deriving Inhabited, Repr, Fintype

inductive Stack : Type
| A | Z
deriving Inhabited, Repr

open Parentheses States Stack

def my_dpda : DPDA States Parentheses Stack :=
  ⟨(fun q x y =>
    match q, x, y with
    | q0, some left,  _ => some (q0, [A, y])
    | q0, some right, A => some (q1, [])
    | _, _, _           => none
    ),
    q0,
    Z,
    (fun y => y = q1),
    (fun _ _ => by simp)
  ⟩
#note "Yayyyyyyyyyyyy!!!!!!!!!!!!!"

-- end Balanced

#check DPDA.transition

/-
The function `DPDA.evalStep desc : Option (InstantDesc M)`
returns the next instantaneous description of the DPDA after performing
*the* transition on the current description, if there exists a transition.
Otherwise, it returns `none`
-/

def evalStep (M : DPDA Q α Γ) (desc : InstantDesc M)
  : Option (InstantDesc M) :=
    have ⟨q, input, stack⟩ := desc

    match input, stack with
    | _, [] => none

    | [], top::rest =>
      match h1 : M.transition q none top with
      | none => none
      | some (q', new_stack) =>
        have h : (a : α) → M.transition q (some a) top = none := by
          intro a
          apply M.h_determinism
          simp [h1]
        some (InstantDesc.mk q' [] (new_stack ++ rest))

    | head::tail, top::rest =>
      match M.transition q (some head) top with
      | none => none
      | some (q', new_stack) =>
        some (InstantDesc.mk q' tail (new_stack ++ rest))

#do_later "Add [@simp] lemmas"

/-
The function `evalFrom`
-/

def evalFrom (M : DPDA Q α Γ) (desc : InstantDesc M) : InstantDesc M :=
  match h : evalStep M desc with
  | none => desc
  | some desc' =>
    match desc.input_tape with
    | [] => desc
    | head::tail => evalFrom M desc'
termination_by desc.input_tape.length
decreasing_by
  simp [evalStep] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · sorry
    -- sorry
  · sorry

def eval (M : DPDA Q α Γ) (input : List α) : (InstantDesc M) :=
  M.evalFrom ⟨M.inital_state, input, [M.initial_stack]⟩

def accepts (M : DPDA Q α Γ) (input : List α) : Prop :=
  let desc := M.eval input
  (M.accept desc.state) ∨ (desc.stack_tape = [] ∧ desc.input_tape = [])

/-
failed to synthesize
  Decidable (my_pda.accepts [left, right, left, right])

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
-- set_option diagnostics true
-- #eval my_dpda.accepts [left, right, left, right]

end DPDA

structure PDA (Q : Type u) (α : Type v) (Γ : Type w) where
  transition : Q → Option α → Γ → Set (Q × List Γ)
  inital_state : Q
  initial_stack : Γ
  accept : Q → Prop

namespace PDA

open PDA

variable {Q : Type u} {α : Type v} {Γ : Type w}

-- Inhabited instance for PDA
instance [Inhabited Q] [Inhabited Γ]: Inhabited (PDA Q α Γ) :=
    ⟨PDA.mk (fun _ _ _ => ∅) (default) (default) (fun _ => default)⟩

/-
An Instantaneous Description of a PDA is a triple (p, w, β) consists of:
-- p is the current state of the PDA
-- w is the remaining input string
-- β is the current stack contents
The stack contents are represented as a list of symbols, with the top of the stack being the head of the list.
-/

structure InstantDesc (M : PDA Q α Γ) where
  state : Q
  input_tape : List α
  stack_tape : List Γ

/-
  We define the step relation on IntantDesc as follows:
  (p, a::x, γ::γs) ⊢ (q, x, γ'++γs)
  iff (q, α) ∈ transition p a A
-/
def step (M : PDA Q α Γ) : (desc₁ : InstantDesc M) → (desc₂ : InstantDesc M) → Prop :=
  fun ⟨p, w, s⟩ ⟨q, w', s'⟩ =>
    (∃ (a : α) (t : Γ) (t' γ : List Γ), w = a::w' ∧ s = t::γ ∧ s' = t'++γ ∧ (q, t') ∈ M.transition p (some a) t)
    ∨ (w = w' ∧ ∃ (t : Γ) (t' γ : List Γ), s = t::γ ∧ (q, t') ∈ M.transition p none t)

-- This checks whether a sequence of InstantDesc is valid through some transitions
def sequenceValid (M : PDA Q α Γ) (desc : List (InstantDesc M)) : Prop :=
  match desc with
  | [] => True
  | _::[] => True
  | head::tailhead::tailtail => M.step head tailhead ∧ sequenceValid M (tailhead::tailtail)

/-
The reflexive and transitive closure of the step relation, meaning any
finite number of step relations, zero, one or `n : Nat`
-/
def stepClosure (M : PDA Q α Γ) : (desc₁ : InstantDesc M) → (desc₂ : InstantDesc M) → Prop :=
  fun desc₁ desc₂ =>
  ∃ (steps : List (InstantDesc M)),
  M.sequenceValid steps
  ∧ steps.head? = some desc₁ ∧ steps.getLast? = some desc₂

/-
# Languages related to PDA
We now define the following two important languages (sets of finite strings over the alphabet α):
1. L(M) = {w ∈ α* | (q₀, w, Z) ⊢* (f, ε, γ) with f ∈ F and γ ∈ Γ*} (final state)
2. N(M) = {w ∈ α* | (q₀, w, Z) ⊢* (q, ε, ε) with q ∈ Q} (empty stack)
-/

def language_final_state (M : PDA Q α Γ) : Language α :=
  {w : List α | ∃ (f : Q) (γ : List Γ), M.step ⟨M.inital_state, w, [M.initial_stack]⟩ ⟨f, [], γ⟩ ∧ M.accept f}

def language_empty_stack (M : PDA Q α Γ) : Language α :=
  {w : List α | ∃ (q : Q), M.step ⟨M.inital_state, w, [M.initial_stack]⟩ ⟨q, [], []⟩}

/-
# Theorem (Equivalence of acceptence by final state and empty stack)
For each pushdown automata M, there exists another PDA M' such that
L(M) = N(M') and N(M) = L(M')
-/

-- We define the following auxilary inductive types
inductive AuxState : Type where
| init : AuxState
| empty : AuxState

inductive MetaStack : Type where
| meta : MetaStack

theorem final_state_equiv_empty_stack {Q' : Type u} {Γ' : Type w} (M : PDA Q α Γ) :
    ∃ (M' M'': PDA Q' α Γ'),
    M.language_final_state = M'.language_empty_stack ∧
    M.language_empty_stack = M''.language_final_state
  := by
    -- We shall construct a new PDA M' such that M' accepts L(M) as well as N(M) by both final state and empty stack
    let Q' : Type u := Q ⊕ AuxState
    let Γ' : Type w := Γ ⊕ MetaStack
    let s : Γ' := Sum.inl M.initial_stack
    let transition' : Q' → Option α → Γ' → Set (Q' × List Γ') :=
      (fun q x y =>
        match q, x, y with
        | init, none, meta => {(M.initial_state, inl M.inital_stack::[meta])}
        )
    sorry
    --let M' : PDA Q' α Γ' := ⟨⟩
