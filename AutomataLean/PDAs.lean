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
#print DFA
#print NFA
#print εNFA

/-
# Pushdown Automata (PDA)
PDAs are a more powerful model of computation than DFAs, as they can accept "context-free languages".
Mathematicaly, a PDA is a 6-tuple (Q, Σ, Γ, δ, q0, F) where
-- Q is a finite set of states
-- Σ is a finite set of input symbols,
-- Γ is a finite set of stack symbols,
-- δ : Q × Σ × Γ → Q × Γ* is the transition function,
-- q0 ∈ Q is the initial state,
-- and F ⊆ Q is the set of accepting states.
-/

structure PDA (Q : Type u) (σ : Type v) (Γ : Type w) where
  /-- A transition function from state to state labelled by the alphabet. -/
  transition : Q → Option σ → Γ → Q × (Language Γ)
  inital_state : Q
  initial_stack : Γ
  accept : Q → Prop

#do_later "Worry about Fintype and Finite later"

namespace PDA

variable {Q : Type u} {σ : Type v} {Γ : Type w} (M: PDA Q σ Γ)

-- Inhabited instance for PDA
instance [Inhabited Q] [Inhabited Γ]: Inhabited (PDA Q σ Γ) :=
    ⟨PDA.mk (fun _ _ _ => (default, default)) (default) (default) (fun _ => default)⟩

/-Example of DFA-/
def my_dfa : DFA Char Bool :=
  { step := (fun q _ => ¬ q)
    start := 0
    accept := fun q => q = true}

#eval my_dfa.eval "sdas".toList

/-- Example of a PDA that accepts the language of balanced parentheses. -/

inductive Parentheses : Type
| left | right
deriving Inhabited, Repr

inductive States : Type
| q0 | q1 | q2
deriving Inhabited, Repr

inductive Stack : Type
| A | Z
deriving Inhabited, Repr

open Parentheses States Stack

def my_pda : PDA States Parentheses Stack :=
  ⟨(fun q x y =>
    match q, x, y with
    | q0, some left,  Z => (q0, {[A, Z]})
    | q0, some left,  A => (q0, {[A, A]})
    | q1, none,       Z => (q1, {[Z]})
    | q1, none,       A => (q1, {[A]})
    | q1, some right, A => (q1, {[]})
    | q2, none,       Z => (q2, {[Z]})
    | _, _, _ => (q2, {[]})
    ),
    q0,
    Z,
    (fun y => y = q0)
  ⟩
#note "Yayyyyyyyyyyyy!!!!!!!!!!!!!"

/-
def PDA.evalFrom {Q : Type u} {σ : Type v} {Γ : Type w} [Finite Γ] (pda : PDA Q σ Γ) (q : Q)
  : (input : List σ) → List Γ → Bool :=
  fun M start stack =>
    match input with
    | [] => pda.accept q
    | x :: xs =>
      let (q', stack') := pda.transition q (some x) (List.headD stack)
      PDA.evalFrom pda xs (stack' ++ stack.tail) q'

#print PDA

end PDA
-/
