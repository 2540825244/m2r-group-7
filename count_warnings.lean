import Lean
open Lean

def analyze (label : String) (path : System.FilePath) : IO Unit := do
  IO.println s!"=== {label} ==="
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .error e => IO.println s!"parse error: {e}"
  | .ok j =>
    match j.getObjVal? "result" with
    | .error e => IO.println s!"no result: {e}"
    | .ok arr =>
      match arr.getArr? with
      | .error e => IO.println s!"not array: {e}"
      | .ok ws =>
        IO.println s!"total warnings: {ws.size}"
        let mut counts : Std.HashMap String Nat := {}
        let mut sorryCount := 0
        let mut checkSorryCount := 0
        let mut sorryFiles : Array (String × String) := #[]
        for w in ws do
          let file := (w.getObjValAs? String "file").toOption.getD "<none>"
          let msg := (w.getObjValAs? String "message").toOption.getD ""
          let line := (w.getObjValAs? Nat "line").toOption.getD 0
          counts := counts.insert file ((counts.getD file 0) + 1)
          let hasDecl := (msg.splitOn "declaration uses").length > 1
          let hasSorry := (msg.splitOn "sorry").length > 1
          if hasDecl && hasSorry then
            sorryCount := sorryCount + 1
            sorryFiles := sorryFiles.push (file, toString line)
          if (msg.splitOn "check_sorry").length > 1 then
            checkSorryCount := checkSorryCount + 1
        IO.println s!"declaration uses sorry: {sorryCount}"
        IO.println s!"check_sorry mentions: {checkSorryCount}"
        IO.println "sorry-bearing files:"
        for (f, l) in sorryFiles do
          IO.println s!"  {f}:{l}"
        IO.println "Focus files (count of warnings):"
        for f in ["M2rGroup7/SixteenClassification/Lemma3.lean", "M2rGroup7/Classification.lean", "M2rGroup7/P2qClassification/P2qClassification.lean"] do
          IO.println s!"  {f}: {counts.getD f 0}"
        IO.println ""

def main : IO Unit := do
  -- We only have the Classification build's warnings file readily available
  analyze "Classification build" "/tmp/.claude/projects/-data-clones-2540825244-m2r-group-7-16-made-easy/d20d2468-6b5d-4542-afc7-bd9478c69cc1/tool-results/mcp-build-tools-get_build_warnings-1780919430912.txt"
