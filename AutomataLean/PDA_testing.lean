import AutomataLean.PDAs
open AutomataLean.PDAs

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
