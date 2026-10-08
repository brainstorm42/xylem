/-
Percolation Extract.lean — post-elaboration declaration extractor for the full pinned corpus.

One `lake env lean --run` target. Imports only `Lean`; at runtime it builds the
elaborated environment via `importModules #[Percolation, Solution]` and folds over
`env.constants`, emitting one JSON record per local `Percolation.*` or `Solution.*` declaration:
pretty-printed per-binder signatures + a best-effort structured term tree,
premise edges (statement vs proof), axioms, kind, doc, source range.

Streams one JSON document to stdout. Loud per-declaration try/catch into
`errors[]`; nonzero exit if any declaration failed. Writes no files itself.

Schema: see the master contract (xylem extractor JSON v1).
-/
import Lean

open Lean Lean.Meta

/-- Fixed pretty-print surface: notation on, short names, no daggers/mvars. -/
def ppOpts (o : Options) : Options :=
  ((((o.setBool `pp.notation true).setBool `pp.unicode.fun true).setBool
    `pp.fullNames false).setBool `pp.privateNames false).setBool `pp.mvars false

/-- Dotted module name that owns a declaration, if any. -/
def isLocalModule (m : Name) : Bool :=
  (`Percolation).isPrefixOf m || m == `Challenge || m == `Solution

def moduleNameOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Nat → JSON number. -/
def jnat (n : Nat) : Json := toJson n

/-- Binder annotation → stable string. -/
def biStr : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

/-- Binder name → JSON, null if anonymous or hygienic (would print a dagger). -/
def hygName (n : Name) : Json :=
  if n.isAnonymous || n.hasMacroScopes then Json.null else Json.str n.toString

/-- Universe level → display string (best effort). -/
def levelStr (l : Level) : String :=
  match l with
  | .zero => "Prop"
  | .succ .zero => "Type"
  | .succ p => "Type " ++ toString p
  | _ => "Sort " ++ toString l

/--
Best-effort structured term tree over the elaborated `Expr`. Implicit and
instance arguments are tagged `explicit:false` (the renderer skips them).
Any form we cannot handle cleanly (bvar leak, mvar, proj, let, over-application)
throws; the caller catches and emits `tree: null`. `topFvars` are the top-level
telescoped binders, so an fvar can be cross-referenced to `binders[].idx`.
-/
partial def toTree (topFvars : Array FVarId) (e : Expr) : MetaM Json := do
  match e with
  | .mdata _ b => toTree topFvars b
  | .const n _ =>
      return Json.mkObj [("node", Json.str "const"), ("name", Json.str n.toString)]
  | .sort l =>
      return Json.mkObj [("node", Json.str "sort"), ("level", Json.str (levelStr l))]
  | .lit (.natVal v) =>
      return Json.mkObj [("node", Json.str "lit"), ("kind", Json.str "nat"),
        ("value", Json.str (toString v))]
  | .lit (.strVal v) =>
      return Json.mkObj [("node", Json.str "lit"), ("kind", Json.str "str"),
        ("value", Json.str v)]
  | .fvar fid =>
      let d ← fid.getDecl
      let idxJson := match topFvars.findIdx? (· == fid) with
        | some i => jnat i
        | none => Json.null
      return Json.mkObj [("node", Json.str "fvar"),
        ("name", hygName d.userName), ("binderIdx", idxJson)]
  | .forallE .. =>
      forallBoundedTelescope e (some 1) fun xs body => do
        let d ← xs[0]!.fvarId!.getDecl
        let bt ← toTree topFvars d.type
        let bodyTree ← toTree topFvars body
        return Json.mkObj [("node", Json.str "forall"),
          ("binderName", hygName d.userName),
          ("binderInfo", Json.str (biStr d.binderInfo)),
          ("binderType", bt), ("body", bodyTree)]
  | .lam .. =>
      lambdaBoundedTelescope e 1 fun xs body => do
        let d ← xs[0]!.fvarId!.getDecl
        let bt ← toTree topFvars d.type
        let bodyTree ← toTree topFvars body
        return Json.mkObj [("node", Json.str "lam"),
          ("binderName", hygName d.userName),
          ("binderType", bt), ("body", bodyTree)]
  | .app .. =>
      let (fnName, allArgs) := e.getAppFnArgs
      -- `OfNat.ofNat _ n _` numeric literal → fold to a lit node
      if fnName == ``OfNat.ofNat && allArgs.size == 3 then
        match allArgs[1]! with
        | .lit (.natVal v) =>
            return Json.mkObj [("node", Json.str "lit"), ("kind", Json.str "nat"),
              ("value", Json.str (toString v))]
        | _ => pure ()
      let fn := e.getAppFn
      let args := e.getAppArgs
      let finfo ← getFunInfo fn (some args.size)
      if finfo.paramInfo.size < args.size then
        throwError "over-application ambiguity"
      let fnTree ← toTree topFvars fn
      let mut argJsons := #[]
      for i in [0:args.size] do
        let explicit := (finfo.paramInfo[i]!).binderInfo.isExplicit
        let vt ← toTree topFvars args[i]!
        argJsons := argJsons.push
          (Json.mkObj [("explicit", Json.bool explicit), ("value", vt)])
      return Json.mkObj [("node", Json.str "app"),
        ("fn", fnTree), ("args", Json.arr argJsons)]
  | .bvar _ => throwError "unsupported_expr:bvar"
  | .mvar _ => throwError "unsupported_expr:mvar"
  | .letE _ _ _ _ _ => throwError "unsupported_expr:let"
  | .proj _ _ _ => throwError "unsupported_expr:proj"

def treeResult (topFvars : Array FVarId) (e : Expr) : MetaM (Json × Option String) := do
  try
    return (← toTree topFvars e, none)
  catch err =>
    let msg ← err.toMessageData.toString
    return (Json.null, some msg)

/-- One declaration → its JSON record (in MetaM; may throw, caught by caller). -/
def emitDecl (env : Environment) (nm : Name) (ci : ConstantInfo) : MetaM Json :=
  withOptions ppOpts do
    forallTelescope ci.type fun xs concl => do
      let topFvars := xs.map (·.fvarId!)
      let mut binders := #[]
      for i in [0:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        let tyText := (← ppExpr d.type).pretty 100
        let (tyTree, tyTreeError) ← treeResult topFvars d.type
        binders := binders.push (Json.mkObj [
          ("idx", jnat i),
          ("name", hygName d.userName),
          ("binderInfo", Json.str (biStr d.binderInfo)),
          ("type", Json.str tyText),
          ("tree", tyTree),
          ("tree_error", match tyTreeError with
            | some msg => Json.str msg
            | none => Json.null)])
      let conclText := (← ppExpr concl).pretty 100
      let (conclTree, conclTreeError) ← treeResult topFvars concl
      -- Whole-signature fallback (the fenced-Lean block a null-tree page renders).
      -- Best-effort: a pp hiccup falls back to `name : type` rather than dropping the decl.
      let sigText ← (try
          let f ← Lean.PrettyPrinter.ppSignature nm
          pure (f.fmt.pretty 100)
        catch _ =>
          let t ← ppExpr ci.type
          pure (nm.toString ++ " : " ++ t.pretty 100))
      let stmtNames := Expr.getUsedConstantsAsSet ci.type
      -- `allowOpaque := true` is load-bearing: `ConstantInfo.value?` defaults it to `false`,
      -- and at that default it returns `none` for `.thmInfo` (Lean 4.31
      -- `Lean/Declaration.lean:482-487`). With the default every THEOREM yielded an empty
      -- proof-premise set — only `def`s (`.defnInfo`, unconditional) produced `in_proof`
      -- edges. The proofs were present all along; this call was declining to look at them.
      let proofNames := match ci.value? (allowOpaque := true) with
        | some v => Expr.getUsedConstantsAsSet v
        | none => ({} : NameSet)
      let mut allSet := stmtNames
      for n in proofNames.toList do
        allSet := allSet.insert n
      let mut prem := #[]
      for n in allSet.toList do
        unless n == nm do
          let modOpt := moduleNameOf env n
          let ext := match modOpt with
            | some m => !isLocalModule m
            | none => true
          prem := prem.push (Json.mkObj [
            ("name", Json.str n.toString),
            ("module", match modOpt with | some m => Json.str m.toString | none => Json.null),
            ("in_type", Json.bool (stmtNames.contains n)),
            ("in_proof", Json.bool (proofNames.contains n)),
            ("external", Json.bool ext),
            ("internal_detail", Json.bool n.isInternalDetail)])
      let axs ← collectAxioms nm
      let doc ← findDocString? env nm
      let rng ← findDeclarationRanges? nm
      let rangeJson := match rng with
        | some r => Json.mkObj [
            ("start", Json.arr #[jnat r.range.pos.line, jnat r.range.pos.column]),
            ("end", Json.arr #[jnat r.range.endPos.line, jnat r.range.endPos.column])]
        | none => Json.null
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec"
        | .quotInfo _ => "quot"
      let modName := (moduleNameOf env nm).getD nm
      let src := (modName.toString.replace "." "/") ++ ".lean"
      return Json.mkObj [
        ("name", Json.str nm.toString),
        ("module", Json.str modName.toString),
        ("src_file", Json.str src),
        ("kind", Json.str kind),
        ("doc", match doc with | some s => Json.str s | none => Json.null),
        ("range", rangeJson),
        ("binders", Json.arr binders),
        ("conclusion", Json.str conclText),
        ("conclusion_tree", conclTree),
        ("conclusion_tree_error", match conclTreeError with
          | some msg => Json.str msg
          | none => Json.null),
        ("signature", Json.str sigText),
        ("premises", Json.arr prem),
        ("internal_detail", Json.bool nm.isInternalDetail),
        ("axioms", Json.arr (axs.map fun a => Json.str a.toString))]

-- `loadExts := true` requires initializers to be enabled first, an `unsafe`
-- action — so the entry point itself is `unsafe` (the LeanDojo `ExtractData`
-- pattern for a standalone environment consumer).
unsafe def main : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  -- `loadExts := true` restores environment extensions (notation + delaborator
  -- attribute state); without it `ppExpr` prints prefix `Eq`/`LE.le` and leaks
  -- `inst✝` instance daggers instead of `=`/`≤`/`‖·‖`.
  let env ← importModules #[
    { module := `Percolation },
    { module := `Solution }] {} (trustLevel := 1024) (loadExts := true)
  -- Batch tool over already-elaborated proofs: disable the (cumulative) heartbeat
  -- limit so a heavy `whnf` mid-corpus can't abort the whole extraction.
  let ctx : Core.Context := { fileName := "<extract>", fileMap := default, maxHeartbeats := 0 }
  let coreAction : CoreM (Array Json × Array Json) := do
    let mut recs := #[]
    let mut errs := #[]
    for (nm, ci) in env.constants.toList do
      match moduleNameOf env nm with
      | some m =>
        if isLocalModule m then
          try
            let j ← MetaM.run' (emitDecl env nm ci)
            recs := recs.push j
          catch e =>
            let msg ← e.toMessageData.toString
            errs := errs.push (Json.mkObj [("name", Json.str nm.toString), ("error", Json.str msg)])
      | none => pure ()
    pure (recs, errs)
  let (recs, errs) ← coreAction.toIO' ctx { env }
  let top := Json.mkObj [
    ("schema_version", jnat 1),
    ("generated_from", Json.str "Solution"),
    ("toolchain", Json.str s!"leanprover/lean4:v{Lean.versionString}"),
    ("capture_projection", Json.mkObj [
      ("status", Json.str "generated_from_elaborated_environment"),
      ("binder_text_complete", Json.bool true),
      ("statement_text_complete", Json.bool true),
      ("expression_trees_included", Json.bool true),
      ("expression_trees_complete", Json.bool false),
      ("tree_diagnostics_included", Json.bool true),
      ("tree_diagnostics_complete", Json.bool true),
      ("proof_terms_included", Json.bool false),
      ("premises_included", Json.bool true),
      ("premises_complete", Json.bool true),
      ("local_module_prefixes", Json.arr #[Json.str "Percolation", Json.str "Challenge", Json.str "Solution"]),
      ("tree_omission_reason", Json.str "Structured expression trees are best-effort per declaration; null trees are retained as an explicit converter fallback. Proof terms are not serialized." )]),
    ("declarations", Json.arr recs),
    ("errors", Json.arr errs)]
  IO.println top.compress
  return (if errs.isEmpty then 0 else 1)
