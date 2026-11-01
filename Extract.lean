import Lean

/-!
Extract the dependency graph of all user declarations under a module prefix as JSON.

Usage: `lake exe extract <RootModule> <Prefix>` e.g. `lake exe extract Foundations Foundations`
Output: JSON array of nodes `{name, kind, module, doc, type, deps, headline, line}`.
-/

open Lean Meta

def skipSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
   "noConfusionType", "sizeOf_spec", "inj", "injEq", "ctorIdx", "toCtorIdx", "ofNat",
   "ctorElimType", "ofNat_ctorIdx", "ctorElim", "mk.injEq", "eq_iff", "ext_iff"]

def isUserDecl (env : Environment) (n : Name) : Bool :=
  !n.isInternal && !isAuxRecursor env n && !isNoConfusion env n && !(env.isProjectionFn n) &&
  !(n.getString!.startsWith "inst") &&
  !(n.components.any fun c => c.toString.startsWith "_" || c.toString.startsWith "match_"
      || c.toString.startsWith "eq_" || c.toString.startsWith "proof_"
      || c.toString == "eq_def" || c.toString == "induct" || c.toString == "mutual_induct"
      || c.toString.startsWith "inst" && false) &&
  !(skipSuffixes.contains n.getString!)

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "recursor"

/-- Constants referenced by an expression (closing over auxiliary definitions). -/
partial def depsOf (env : Environment) (keep : Name → Bool) (ownMod : Name → Bool) (e : Expr) : StateM NameSet Unit := do
  for c in e.getUsedConstants do
    if (← get).contains c then continue
    modify (·.insert c)
    if !keep c then
      -- look through auxiliary constants (match_, proof_, eq_ lemmas ...) to their deps
      if let some ci := env.find? c then
        if c.isInternal || ownMod c || (c.components.any fun x => x.toString.startsWith "match_" || x.toString.startsWith "proof_" || x.toString.startsWith "_") then
          depsOf env keep ownMod ci.type
          if let some v := (ci.value? (allowOpaque := true)) then depsOf env keep ownMod v

def escape (s : String) : String := s.quote

unsafe def main (args : List String) : IO Unit := do
  let root := (args.headD "Foundations").toName
  let pfx := (args.getD 1 "Foundations").toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let modIdxOf := fun (n : Name) => env.getModuleIdxFor? n
  let inPrefix := fun (n : Name) =>
    match modIdxOf n with
    | some i => pfx.isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let decls := env.constants.toList.filter fun (n, ci) =>
    inPrefix n && isUserDecl env n && !(ci matches .recInfo _) && !(ci matches .ctorInfo _)
  let keepSet : NameSet := decls.foldl (fun s (n, _) => s.insert n) {}
  let keep := fun n => keepSet.contains n
  let ctx : Core.Context := { fileName := "<extract>", fileMap := default, maxHeartbeats := 0 }
  let cstate : Core.State := { env }
  let (out, _) ← (do
    let mut items : Array String := #[]
    for (n, ci) in decls do
      let ty ← (do
        let fmt ← MetaM.run' (ppExpr ci.type)
        pure (toString fmt)) <|> pure "?"
      let doc := (← findDocString? env n).getD ""
      let ((), used) := (do
          depsOf env keep inPrefix ci.type
          if let some v := (ci.value? (allowOpaque := true)) then depsOf env keep inPrefix v).run {}
      let deps := used.toList.filter fun d => keep d && d != n
      let modName := match modIdxOf n with
        | some i => env.header.moduleNames[i.toNat]!.toString
        | none => ""
      let rng ← findDeclarationRanges? n
      let line := match rng with
        | some r => r.range.pos.line
        | none => 0
      let endLine := match rng with
        | some r => r.range.endPos.line
        | none => 0
      let axs ← (do let a ← Lean.collectAxioms n; pure a) <|> pure #[]
      let axJson := ",".intercalate (axs.toList.map fun a => escape a.toString)
      let headline := (String.ofList (doc.toList.dropWhile Char.isWhitespace)).startsWith "**"
      let depsJson := ",".intercalate (deps.map fun d => escape d.toString)
      items := items.push <|
        "{\"name\":" ++ escape n.toString ++ ",\"kind\":" ++ escape (kindOf ci) ++
        ",\"module\":" ++ escape modName ++ ",\"line\":" ++ toString line ++ ",\"end\":" ++ toString endLine ++
        ",\"headline\":" ++ toString headline ++
        ",\"doc\":" ++ escape doc ++ ",\"type\":" ++ escape ty ++
        ",\"deps\":[" ++ depsJson ++ "],\"axioms\":[" ++ axJson ++ "]}"
    pure items : CoreM (Array String)).toIO ctx cstate
  -- module docstrings
  let mut mods : Array String := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if pfx.isPrefixOf m then
      let docs := getModuleDoc? env m |>.getD #[]
      let text := "\n\n".intercalate (docs.toList.map (·.doc))
      mods := mods.push ("{\"module\":" ++ escape m.toString ++ ",\"doc\":" ++ escape text ++ "}")
  IO.println ("{\"nodes\":[\n" ++ ",\n".intercalate out.toList ++ "\n],\"modules\":[\n" ++
    ",\n".intercalate mods.toList ++ "\n]}")
