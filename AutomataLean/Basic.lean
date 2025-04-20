import Lean

open Lean Meta Elab Term Tactic

syntax "#note" str : command
syntax "#do_later" str : command


elab_rules : command
  | `(#note $s:str) => do
    let msg := s.getString
    logInfo m!"NOTE: {msg}"
  | `(#do_later $s:str) => do
    let msg := s.getString
    logInfo m!"TODO: {msg}"

elab "todo" s:str : tactic =>
  withMainContext do
    let msg := s.getString
    logWarning m!"TODO: {msg}"
    let target ← getMainTarget
    let t ← mkAppM ``sorryAx #[target, mkConst ``false]
    closeMainGoal `todo t
