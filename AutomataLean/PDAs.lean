import AutomataLean.Basic
import AutomataLean.Parsing
import Mathlib

universe u v w

open Computability
open Relation
open Symbol

/-
# Pushdown Automata (PDA)

PDAs are a more powerful model of computation than DFAs, as they can accept "context-free languages".
Mathematicaly, a PDA is a 6-tuple (Q, Σ, Γ, δ, q0, F) where
-- Q is a finite set of states
-- Σ is a finite set of input symbols,
-- Γ is a finite set of stack symbols,
-- δ : Q × Σ × Γ → Set (Q × Γ*`) is the transition function,
-- q₀ ∈ Q is the initial state,
-- and F ⊆ Q is the set of accepting states.
-/

structure PDA (Q : Type u) (α : Type v) (Γ : Type w) where
  transition : Q → Option α → Γ → Set (Q × List Γ)
  inital_state : Q
  initial_stack : Γ
  accept : Q → Prop

namespace PDA

open PDA

variable {Q : Type u} {α : Type v} {Γ : Type w}

def start_symbol (Γ : Type w) [Inhabited Γ] : Γ := default

local notation (priority := high) "$" => start_symbol

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

def stepClosure (M : PDA Q α Γ ) := Relation.ReflTransGen M.step

lemma stepClosure_equiv (M : PDA Q α Γ) : M.stepClosure =
  (fun desc₁ desc₂ =>
  ∃ (steps : List (InstantDesc M)),
  M.sequenceValid steps
  ∧ steps.head? = some desc₁ ∧ steps.getLast? = some desc₂)
:= by sorry

/-
# Languages related to PDA
We now define the following two important languages (sets of finite strings over the alphabet α):
1. L(M) = {w ∈ α* | (q₀, w, Z) ⊢* (f, ε, γ) with f ∈ F and γ ∈ Γ*} (final state)
2. N(M) = {w ∈ α* | (q₀, w, Z) ⊢* (q, ε, ε) with q ∈ Q} (empty stack)
-/

def language_final_state (M : PDA Q α Γ) : Language α :=
  {w : List α | ∃ (f : Q) (γ : List Γ), M.stepClosure ⟨M.inital_state, w, [M.initial_stack]⟩ ⟨f, [], γ⟩ ∧ M.accept f}

def language_empty_stack (M : PDA Q α Γ) : Language α :=
  {w : List α | ∃ (q : Q), M.stepClosure ⟨M.inital_state, w, [M.initial_stack]⟩ ⟨q, [], []⟩}

/-
# Theorem (Equivalence of acceptence by final state and empty stack)
For each pushdown automata M, there exists another PDA M' such that
L(M) = N(M') and N(M) = L(M')
-/

-- We define the following auxilary inductive types in order to help prove the theorem
inductive AuxState : Type where
| init : AuxState
| empty : AuxState
deriving Inhabited, Repr, Fintype, DecidableEq

inductive MetaStack : Type where
| meta : MetaStack
deriving Inhabited, Repr, Fintype, DecidableEq

theorem final_state_equiv_empty_stack {Q : Type u} {α : Type v} {Γ : Type w} (M : PDA Q α Γ) [Fintype Q] :
    ∃ (Q₁ : Type u) (Γ₁ : Type w) (M' M'': PDA Q₁ α Γ₁),
    M.language_final_state = M'.language_empty_stack ∧
    M.language_empty_stack = M''.language_final_state
  := by
    -- We shall construct a new PDA M' such that M' accepts L(M) as well as N(M) by both final state and empty stack
    let Q' : Type u := Q ⊕ AuxState
    let Γ' : Type w := Γ ⊕ MetaStack
    let q₀ : Q' := Sum.inl M.inital_state
    let s : Γ' := Sum.inl M.initial_stack
    -- let q₀ : StatePrime Q := StatePrime.inl M.inital_state
    -- let s : StackPrime Γ := StackPrime.inl M.initial_stack

    have h₀ : q₀.isLeft = true := by
      simp only [q₀, Sum.isLeft_inl]
    have h₁ : s.isLeft = true := by
      simp only [s, Sum.isLeft_inl]

    have decide (q : Q) : Decidable (M.accept q) := by
      apply Classical.dec

    let primeCast : Set (Q × List Γ) → Set (Q' × List Γ') :=
      Set.image (Prod.map Sum.inl <| List.map Sum.inl)

    let transition' : Q' → Option α → Γ' → Set (Q' × List Γ') :=
      (fun q a x =>
        match q, a, x with
        | Sum.inr AuxState.init, none, Sum.inr MetaStack.meta => {(q₀, [x])}
        | Sum.inr AuxState.empty, none, _ => {(Sum.inr AuxState.empty, [])}
        | Sum.inl q', none, Sum.inr MetaStack.meta =>
          if M.accept q' then
            {(Sum.inr AuxState.empty, [Sum.inr MetaStack.meta])}
          else
            ∅
        | Sum.inl q', none, Sum.inl X =>
          if M.accept q' then
            {(Sum.inr AuxState.empty, [Sum.inl X])}
          else
            primeCast (M.transition q' none X)
        | Sum.inl q', some a', Sum.inl X =>
          primeCast (M.transition q' (some a') X)
        | _, _, _ =>
          ∅
      )

    let accept' : Q' → Prop :=
      fun q =>
        match q with
        | Sum.inr AuxState.empty => True
        | _ => False

    let transition'' : Q' → Option α → Γ' → Set (Q' × List Γ') :=
      (fun q a x =>
        match q, a, x with
        | Sum.inr AuxState.init, none, Sum.inr MetaStack.meta =>
            {(q₀, [s, x])}
        | Sum.inl q', none, Sum.inr MetaStack.meta =>
            {(Sum.inr AuxState.empty, [x])}
        | Sum.inr AuxState.empty, none, Sum.inr MetaStack.meta =>
            {(q, [])}
        | Sum.inl q', _, Sum.inl x' =>
            primeCast (M.transition q' a x')
        | _, _, _ =>
            ∅
      )

    have M' : PDA Q' α Γ' := ⟨transition', q₀, s, accept'⟩
    have M'' : PDA Q' α Γ' := ⟨transition'', q₀, s, accept'⟩

    use Q', Γ', M', M''

    have h_part₁ : M.language_final_state = M'.language_empty_stack := by
      apply Set.ext
      intro x
      constructor
      · simp only [language_final_state, language_empty_stack]
        intro
        simp only [Set.mem_setOf_eq] at *

        sorry
      · sorry

    have h_part₂ : M.language_empty_stack = M''.language_final_state := sorry

    use h_part₁, h_part₂

#do_later "Complete this proof!"

/-
# Context-Free Grammars

A context-free grammar is a formal grammar that consists of a set of production rules used to generate strings in a context-free language. It is defined as a 4-tuple (V, Σ, R, S) where:
-- V is a finite set of variables (non-terminal symbols),
-- Σ is a finite set of terminal symbols (disjoint from V),
-- R is a finite set of production rules of the form A → w, where A ∈ V and w ∈ (V ∪ Σ)*,
-- S ∈ V is the start variable.

Context-free grammars are used to describe the syntax of programming languages and are equivalent in power to pushdown automata.

CFGs have already been implemented in `Mathlib.Computability`
-/

/-
structure ContextFreeGrammar.{u_1} (T : Type u_1) : Type (max 1 u_1)
number of parameters: 1
fields:
  ContextFreeGrammar.NT : Type
  ContextFreeGrammar.initial : self.NT
  ContextFreeGrammar.rules : Finset (ContextFreeRule T self.NT)
constructor:
  ContextFreeGrammar.mk.{u_1} {T : Type u_1} (NT : Type) (initial : NT) (rules : Finset (ContextFreeRule T NT)) :
    ContextFreeGrammar T
-/
#print ContextFreeGrammar

/-
  ## The language generated by a context-free grammar is the set of strings that can be derived from the start variable using the production rules.
  It is called a `Context-Free Language (CFL)`
-/

/-
  def ContextFreeGrammar.language.{u_1} : {T : Type u_1} → ContextFreeGrammar T → Language T :=
  fun {T} g ↦ {w | g.Generates (List.map Symbol.terminal w)}
-/
#print ContextFreeGrammar.language


-- Now, we prove some results about PDAs and CFGs

-- A language is context-free, iff there exists a PDA accepting it.
-- That is, CFGs and PDAs are equivalent in computing power.

inductive QCfg : Type u where
| q_start : QCfg
| q_loop : QCfg
| q_accept : QCfg

inductive ΓCfg {α : Type v} (G : ContextFreeGrammar α) where
| empty : ΓCfg G
| start : ΓCfg G
| term (a : α) : ΓCfg G
| production : (A : G.NT) → ΓCfg G

def symbolToΓ {α : Type v} {G : ContextFreeGrammar α} (s : Symbol α G.NT) : ΓCfg G :=
  match s with
  | Symbol.terminal t => ΓCfg.term t
  | Symbol.nonterminal A => ΓCfg.production A

local notation (priority := high) "q₀" => QCfg.q_start
local notation (priority := high) "q₁" => QCfg.q_loop
local notation (priority := high) "q₂" => QCfg.q_accept

local notation (priority := high) "$" => ΓCfg.empty

-- instance h {G : ContextFreeGrammar α} (x : QCfg × List ΓCfg) (A : G.NT) : Decidable (x.1 = q₁ ∧ ∃ (p : ContextFreeRule α G.NT), p ∈ G.rules ∧ A = p.input ∧ x.2 = List.map symbolToΓ p.output)

lemma language_context_free_implies_exists_PDA (G : ContextFreeGrammar α) :
  ∃ (Q : Type u) (Γ: Type v) (M : PDA Q α Γ) (h : Fintype Q),
  G.language = M.language_empty_stack
:= by
  -- We need to construct a PDA from the CFG
  let Q : Type u := QCfg
  let Γ := ΓCfg G

  #check Γ
  #check Q × List Γ
  #check Set (Q × List Γ)
  #check G.rules

  have h (x : Q × List Γ) (A : G.NT) : Decidable (x.1 = q₁ ∧ ∃ (p : ContextFreeRule α G.NT), p ∈ G.rules ∧ A = p.input ∧ x.2 = List.map symbolToΓ p.output) := by apply Classical.dec

  let transition : Q → Option α → Γ → Set (Q × List Γ) :=
  (fun q a x =>
      match q, a, x with
      | q₀, none, ΓCfg.empty => {(q₁, [ΓCfg.start, ΓCfg.empty])}
      | q₁, none, ΓCfg.production A =>
        (fun (q, l) =>
          have h₀ := h (q, l)
          if q = q₁ ∧ ∃ (p : ContextFreeRule α G.NT), p ∈ G.rules ∧ A = p.input ∧ l = List.map symbolToΓ p.output then
            True
          else
            False
        )
      | q₁, some _, ΓCfg.term _ => {(q₂, [])}
      | _, _, _ => ∅
  )

  let initial_state : Q := q₀
  let initial_stack : Γ := ΓCfg.start

  let M : PDA Q α Γ := ⟨transition, initial_state, initial_stack, (· = q₂)⟩

  have hQ : Fintype Q := by sorry

  use Q, Γ, M, hQ
  ext
  unfold ContextFreeGrammar.language ContextFreeGrammar.Generates ContextFreeGrammar.Derives ContextFreeGrammar.Produces
  unfold PDA.language_empty_stack PDA.stepClosure

  #check Relation.ReflTransGen

lemma language_PDA_implies_exists_cfg (L : Language α) (M : PDA Q α Γ)
  (h : L = M.language_empty_stack ∨ L = M.language_final_state) [Fintype Q]:
  ∃ (G : ContextFreeGrammar α), G.language = L := by sorry

/- Finally, we can use the two directions to prove the theorem -/
theorem PDA_equiv_CFG {L : Language α} :
  (∃ (Q : Type u) (Γ : Type v) (M : PDA Q α Γ) (hF : Fintype Q), L = M.language_empty_stack ∨ L = M.language_final_state) ↔ L.IsContextFree
  := by
  constructor
  · intro a
    rcases a with ⟨Q, Γ, M, h⟩
    rcases h with ⟨_, h₁⟩
    unfold Language.IsContextFree
    exact language_PDA_implies_exists_cfg L M h₁
  · intro a
    unfold Language.IsContextFree at a
    rcases a with ⟨G, h⟩
    have h₁ := language_context_free_implies_exists_PDA G
    rcases h₁ with ⟨Q, Γ, M, hQ, h₂⟩
    apply Eq.trans (Eq.symm h) at h₂
    use Q, Γ, M, hQ
    apply Or.inl
    exact h₂

/-
  Since a DFA can be simulated by a PDA, all regular languages are context-free
-/
theorem regular_implies_context_free (L : Language α) (h : L.IsRegular) : (L.IsContextFree) := by
  unfold Language.IsRegular at h
  rcases h with ⟨Q, h₁, M, final⟩
  -- A DFA can be simulated by a PDA by ignoring the stack entirely.
  let Q' := Q
  let Γ' := Unit

  let transition : Q' → Option α → Γ' → Set (Q' × List Γ') :=
    (fun q a x =>
      match q, a, x with
      | q, some a', _ => {(M.step q a', [])}
      | _, _, _ => ∅
    )

  let initial_state : Q' := M.start
  let initial_stack : Γ' := Unit.unit
  let accept : Q' → Prop := M.accept

  let M' : PDA Q' α Γ' := ⟨transition, initial_state, initial_stack, accept⟩
  have hQ : Fintype Q' := by apply h₁

  have h₁ : M.accepts = M'.language_final_state := by
    sorry

  unfold Language.IsContextFree
  apply language_PDA_implies_exists_cfg L M'
  apply Or.inr
  exact Eq.trans (Eq.symm final) h₁

/-
# Non-Context-Free Languages
There exist Languages that are not Context-Free.
A key and powerful result that is often very helpful in proving that a given language is not Context-Free
is the `Pumping Lemma for CFLs`.
This is akin to the Pumping Lemma for Regular Languages, proven in `Mathlib.Computability.DFA.pumping_lemma`
-/


/-
# Theorem : Pumping Lemma for Context-Free Languages
If `L` is a context-free language,
then there is a number `p` (the pumping length) where, if `w` is any string in `L` of
length at least `p`, then `s` may be divided into five pieces `w = uvxyz` satisfying the
conditions
1. For each `i ≥ 0, u(v^i)x(y^i)z ∈ L`,
2. `|vy| > 0`, and
3. `|vxy| ≤ p`.

When `s` is being divided into `uvxyz`, condition 2 says that either `v` or `y` is not
the empty string. Otherwise the theorem would be trivially true. Condition 3
states that the pieces `v`, `x`, and `y` together have length at most `p`. This technical
condition is sometimes useful in proving that certain languages are not context
free.
-/

def mulList (l : List α) (n : Nat) : List α :=
  match n with
  | 0 => []
  | m + 1 => l ++ mulList l m

-- We synthesizse an instance of HMul to allow writing `w*n` for `w ... w` (repeated n times)
instance listHMul : HMul (List α) Nat (List α) where
  hMul := mulList

theorem pumping_lemma (L : Language α) (h : L.IsContextFree) :
  ∃ (p : Nat),
  ∀ w ∈ L, w.length ≥ p →
  (
    ∃ (u v x y z : List α),
      (
        (i : Nat) → (u ++ v*i ++ x ++ y*i ++ z ∈ L) ∧
        v.length + y.length > 0 ∧
        v.length + x.length + y.length ≤ p
      )
  )
:= by
