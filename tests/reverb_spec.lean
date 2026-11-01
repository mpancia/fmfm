import Spec.Reverb

/-! Reads the lines tests/reverb_spec_diff.c prints and recomputes both wet samples from `Spec/Reverb.lean`.
Any sample where the spec and the glue disagree is printed; the count is the exit code. -/

def Reverb.specLeftRight (v : Array Int32) : Int32 × Int32 :=
  let input := Reverb.diffuse v[0]! v[1]! v[2]! v[6]! v[7]! v[8]! v[9]!
  let left := Reverb.mul (Reverb.loop input v[10]! v[5]! v[11]! v[12]! v[3]! v[4]! v[2]!) 65536
  let right := Reverb.mul (Reverb.loop input v[15]! v[14]! v[16]! v[17]! v[3]! v[4]! (-v[2]!)) 65536
  (left, right)

/-- Reads the glue's lines from stdin, compares, exits 1 on any disagreement. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut bad := 0
  let mut count := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let words := (line.splitOn " ").map fun w => (w.splitOn "\n").headD ""
    let v := (words.filter (· != "")).toArray.map fun w => Int32.ofInt w.toInt!
    if v.size != 19 then
      IO.println s!"bad line: {line}"
      bad := bad + 1
    else
      count := count + 1
      let (left, right) := Reverb.specLeftRight v
      if left != v[13]! || right != v[18]! then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"sample {count}: spec {left} {right}, glue {v[13]!} {v[18]!}"
  IO.println s!"reverb spec: {count} samples, {bad} disagree with the glue"
  return if bad == 0 then 0 else 1
