import AutomataLean.PDAs
open AutomataLean.PDAs

/-
The following code defines a simple pushdown automaton (PDA) that recognizes the language of balanced parentheses.
The PDA has two states (q0 and q1), two types of parentheses (left and right), and a stack that can contain either an 'A' or a 'Z'.
The PDA transitions are defined as follows:
- q0, left, Z -> (q0, [A, Z])
- q0, left, A -> (q0, [A, A])
- q0, right, A -> (q1, [])
- q1, right, A -> (q1, [])
- q1, right, Z -> (q1, [])
The PDA accepts the input if it ends in state q1 and the stack is empty.

-/

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

def my_pda : PDA States Parentheses Stack :=
  ⟨(fun q x y =>
    match q, x, y with
    | q0, some left,  _ => {some (q0, [A, y])}
    | q0, some right, A => {some (q1, [])}
    | _, _, _           => {none}
    ),
    q0,
    Z,
    (fun y => y = q1),
    (fun _ _ => by simp)
  ⟩
