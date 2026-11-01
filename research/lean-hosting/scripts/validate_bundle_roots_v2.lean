-- DRAFT: exact native root preflight only. Never invokes an exporter or compiler.
import Lean
open Lean

private def requestProfile := "ansatz-exact-root-request/1"
private def evidenceProfile := "ansatz-exact-root-evidence/1"
private def pinnedHash := "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
private def maxBytes := 16777216
private def maxRoots := 100000
private def maxSegments := 1024

private def reject (message : String) : IO α :=
  throw <| IO.userError message

private def decimal (text : String) (bound : Nat) : IO Nat := do
  unless !text.isEmpty && text.length ≤ 19 && (text == "0" || !text.startsWith "0") &&
      text.toList.all (fun c => '0' ≤ c && c ≤ '9') do
    reject "Noncanonical decimal request field"
  let some value := text.toNat? | reject "Invalid decimal request field"
  unless value ≤ bound do reject "Request numeric bound exceeded"
  return value

private def hexDigit (c : Char) : IO Nat := do
  if '0' ≤ c && c ≤ '9' then return c.toNat - '0'.toNat
  if 'a' ≤ c && c ≤ 'f' then return c.toNat - 'a'.toNat + 10
  reject "Noncanonical lowercase hexadecimal request field"

private def unhex (text : String) : IO String := do
  let chars := text.toList.toArray
  unless chars.size % 2 == 0 do reject "Odd hexadecimal request field"
  let mut bytes := ByteArray.empty
  for index in [0:chars.size / 2] do
    let high ← hexDigit chars[2 * index]!
    let low ← hexDigit chars[2 * index + 1]!
    bytes := bytes.push (UInt8.ofNat (16 * high + low))
  let some result := String.fromUTF8? bytes | reject "Invalid UTF-8 request string"
  return result

private structure RootRequest where
  text : String
  expected : Name
  deriving Inhabited

private structure RoleRequest where
  role : String
  iteration : Nat
  roots : Array RootRequest

private def parseRoot (line : String) : IO RootRequest := do
  let fields := (line.splitOn "\t").toArray
  unless fields.size ≥ 3 do reject "Malformed root request row"
  let text ← unhex fields[0]!
  unless !text.isEmpty do reject "Empty native root text"
  let count ← decimal fields[1]! maxSegments
  unless count > 0 && fields.size == count + 2 do reject "Wrong Name segment count"
  let mut expected := Name.anonymous
  for index in [0:count] do
    let field := fields[index + 2]!
    if field.startsWith "s:" then
      expected := .str expected (← unhex (field.drop 2).toString)
    else if field.startsWith "n:" then
      -- Match the current Java bridge's explicit supported numeric domain.
      expected := .num expected (← decimal (field.drop 2).toString 9223372036854775807)
    else
      reject "Unknown Name segment tag"
  return { text, expected }

private def parseRequests (bytes : ByteArray) : IO (Array RoleRequest) := do
  unless bytes.size ≤ maxBytes do reject "Request byte bound exceeded"
  let some text := String.fromUTF8? bytes | reject "Invalid UTF-8 request file"
  unless text.endsWith "\n" do reject "Request requires final LF"
  let lines := (text.splitOn "\n").toArray
  unless lines.size ≥ 3 && lines[0]! == requestProfile do reject "Wrong request framing"
  let roleCount ← decimal lines[1]! 3
  unless roleCount > 0 do reject "Empty role request"
  let mut position := 2
  let mut total := 0
  let mut previousRole := 0
  let mut result : Array RoleRequest := #[]
  for _ in [0:roleCount] do
    unless position < lines.size - 1 do reject "Truncated role request"
    let fields := (lines[position]!.splitOn "\t").toArray
    position := position + 1
    unless fields.size == 3 do reject "Malformed role header"
    let role := fields[0]!
    let roleNumber := if role == "init" then 1 else if role == "lex" then 2
      else if role == "sizeof" then 3 else 0
    unless roleNumber > previousRole do reject "Unknown, duplicate or unordered role"
    previousRole := roleNumber
    let iteration ← decimal fields[1]! 1000000
    let rootCount ← decimal fields[2]! maxRoots
    unless rootCount > 0 && total + rootCount ≤ maxRoots do reject "Invalid total root count"
    total := total + rootCount
    let mut roots : Array RootRequest := #[]
    let mut texts : Std.HashSet String := {}
    let mut names : Std.HashSet Name := {}
    for _ in [0:rootCount] do
      unless position < lines.size - 1 do reject "Truncated root request"
      let root ← parseRoot lines[position]!
      position := position + 1
      unless !texts.contains root.text && !names.contains root.expected do
        reject "Duplicate root text or structured identity within role"
      texts := texts.insert root.text
      names := names.insert root.expected
      roots := roots.push root
    result := result.push { role, iteration, roots }
  unless position == lines.size - 1 && lines[position]! == "" do
    reject "Trailing data or incorrect request counts"
  return result

private def rootFailure (env : Environment) (root : RootRequest) : Option String :=
  if root.text.startsWith "--" then some "option-like-root"
  else if root.text.toList.any (· == '\x00') then some "nul-root"
  else match Syntax.decodeNameLit ("`" ++ root.text) with
    | none => some "invalid-name-syntax"
    | some actual =>
      if actual != root.expected then some "decoded-name-mismatch"
      else if !env.contains root.expected then some "missing-exact-root"
      else none

def main (args : List String) : IO UInt32 := do
  unless Lean.githash == pinnedHash && Lean.versionString == "4.33.1" do
    reject "Wrong pinned Lean producer"
  let [path] := args | reject "Expected exactly one framed request path"
  let bytes ← IO.FS.readBinFile path
  let requests ← parseRequests bytes
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let mut checked := 0
  let mut rejected := 0
  let mut failures : Array Json := #[]
  let mut roles : Array Json := #[]
  for request in requests do
    let mut roleRejected := 0
    for index in [0:request.roots.size] do
      checked := checked + 1
      if let some reason := rootFailure env request.roots[index]! then
        rejected := rejected + 1
        roleRejected := roleRejected + 1
        -- Diagnostics are bounded; counts still include EVERY rejected root.
        if failures.size < 64 then
          failures := failures.push <| Json.mkObj
            [("role", toJson request.role), ("iteration", toJson request.iteration),
             ("root", toJson index), ("reason", toJson reason)]
    roles := roles.push <| Json.mkObj
      [("role", toJson request.role), ("iteration", toJson request.iteration),
       ("roots", toJson request.roots.size), ("rejected", toJson roleRejected)]
  IO.println (Json.mkObj
    [("profile", toJson evidenceProfile),
     ("lean", Json.mkObj [("version", toJson Lean.versionString), ("githash", toJson Lean.githash)]),
     ("requestBytes", toJson bytes.size), ("checked", toJson checked),
     ("rejected", toJson rejected), ("roles", Json.arr roles),
     ("failures", Json.arr failures)]).compress
  return if rejected == 0 then 0 else 2
