import ChowStanley
import Lean

/-!
# Axiom audit

Enumerates every declaration in the `ChowStanley` namespace **from the environment**
(not from a hand-written list) and reports the axioms each depends on.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut rows : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.toList do
    if (`ChowStanley).isPrefixOf n then
      if n.isInternal then continue
      if (← n.isBlackListed) then continue
      let ax ← Lean.collectAxioms n
      rows := rows.push (n, ax)
  let sorted := rows.qsort (fun a b => a.1.toString < b.1.toString)
  let mut nAxFree := 0
  let mut nPropQuot := 0
  let mut nChoice := 0
  let mut nOther := 0
  for (n, ax) in sorted do
    let s := ax.map (·.toString)
    let hasChoice := s.contains "Classical.choice"
    let hasSorry := s.contains "sorryAx"
    let allowed := s.all (fun a => a == "propext" || a == "Quot.sound")
    if hasSorry then
      nOther := nOther + 1
      logInfo m!"SORRY  {n} : {ax}"
    else if ax.isEmpty then
      nAxFree := nAxFree + 1
      logInfo m!"AXIOM-FREE  {n}"
    else if allowed then
      nPropQuot := nPropQuot + 1
      logInfo m!"prop/quot   {n} : {ax}"
    else if hasChoice then
      nChoice := nChoice + 1
      logInfo m!"CHOICE      {n} : {ax}"
    else
      nOther := nOther + 1
      logInfo m!"OTHER       {n} : {ax}"
  logInfo m!"TOTAL {sorted.size} | axiom-free {nAxFree} | propext/Quot.sound {nPropQuot} | Classical.choice {nChoice} | other/sorry {nOther}"
  -- ★門: 自己申告でなく、ここが落ちれば `lake env lean` が非ゼロで終了する
  if nChoice != 0 then
    throwError "AUDIT FAILED: {nChoice} declaration(s) depend on Classical.choice"
  if nOther != 0 then
    throwError "AUDIT FAILED: {nOther} declaration(s) depend on sorryAx or an unexpected axiom"
  if sorted.size < 100 then
    throwError "AUDIT FAILED: only {sorted.size} declarations found; the audit window is wrong"
