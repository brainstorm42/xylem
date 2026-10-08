/-
ExtractProofTrace.lean — structural proof artifacts for the reachable Solution proof cone.

This is deliberately separate from the full declaration capture.  The full
capture records every elaborated declaration and every type/proof constant use;
this file retains the actual elaborated Expr tree for the named proof-boundary
declarations.  It is a structural artifact, not a pretty mathematical proof
and not a serialization of opaque proof constants hidden behind those names.

The traversal starts at the public endpoint and follows every local constant
reachable from each retained elaborated value in deterministic breadth-first
order.  Each maximal application spine is retained as an application record.
Local theorem/constructor/opaque/axiom heads and free-variable assumptions
receive exact argument/type/context mappings; external and definitional
applications remain in the structural inventory with an explicit
`structural_only` status. Constants reached through binder types are emitted
as `type_only_reference` records and are never inferred to be proof
applications. Data-valued applications remain in the trace as data evidence;
only applications whose instantiated result is a proposition are promoted as
proof terms.
-/
import Lean

open Lean Lean.Meta

def treeFuel : Nat := 50000

def biText : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

def litText : Literal → String
  | .natVal v => "nat:" ++ toString v
  | .strVal v => "str:" ++ v

def lookup (env : Environment) (nm : Name) : Option ConstantInfo :=
  env.find? nm

/- A total structural view: unlike the human-oriented signature renderer, this
   view does not reject let/projection/bvar/mvar nodes.  A fuel marker is
   explicit if a future proof exceeds the artifact bound. -/
partial def proofTree (fuel : Nat) (e : Expr) : Json :=
  if fuel == 0 then
    Json.mkObj [("node", Json.str "truncated"), ("fuel", Json.bool true)]
  else
    let next := fuel - 1
    match e with
    | .bvar i => Json.mkObj [("node", Json.str "bvar"), ("index", toJson i)]
    | .fvar _ => Json.mkObj [("node", Json.str "fvar")]
    | .mvar _ => Json.mkObj [("node", Json.str "mvar")]
    | .sort l => Json.mkObj [("node", Json.str "sort"), ("level", Json.str (toString l))]
    | .const n ls => Json.mkObj [
        ("node", Json.str "const"), ("name", Json.str n.toString),
        ("levels", Json.arr (ls.toArray.map fun l => Json.str (toString l)))]
    | .app f a => Json.mkObj [
        ("node", Json.str "app"), ("fn", proofTree next f), ("arg", proofTree next a)]
    | .lam n ty body bi => Json.mkObj [
        ("node", Json.str "lam"), ("name", Json.str n.toString),
        ("binderInfo", Json.str (biText bi)), ("type", proofTree next ty),
        ("body", proofTree next body)]
    | .forallE n ty body bi => Json.mkObj [
        ("node", Json.str "forall"), ("name", Json.str n.toString),
        ("binderInfo", Json.str (biText bi)), ("type", proofTree next ty),
        ("body", proofTree next body)]
    | .letE n ty value body nondep => Json.mkObj [
        ("node", Json.str "let"), ("name", Json.str n.toString),
        ("nondep", Json.bool nondep), ("type", proofTree next ty),
        ("value", proofTree next value), ("body", proofTree next body)]
    | .lit l => Json.mkObj [("node", Json.str "lit"), ("value", Json.str (litText l))]
    | .mdata _ body => Json.mkObj [("node", Json.str "mdata"), ("body", proofTree next body)]
    | .proj n i body => Json.mkObj [
        ("node", Json.str "proj"), ("structure", Json.str n.toString),
        ("index", toJson i), ("body", proofTree next body)]

def localDeclKindText : LocalDeclKind → String
  | .default => "default"
  | .implDetail => "implementation_detail"
  | .auxDecl => "auxiliary"

def localContextSnapshot : MetaM Json := do
  let lctx ← getLCtx
  let mut entries := #[]
  for fvarId in lctx.getFVarIds do
    let d ← fvarId.getDecl
    let isProp ← try isProp d.type catch _ => pure false
    let ty ← ppExpr d.type
    entries := entries.push <| Json.mkObj [
      ("index", toJson d.index),
      ("name", Json.str d.userName.toString),
      ("binderInfo", Json.str (biText d.binderInfo)),
      ("kind", Json.str (localDeclKindText d.kind)),
      ("type", Json.str (ty.pretty 100)),
      ("is_proposition", Json.bool isProp)]
  return Json.arr entries

def exprKindText : Expr → String
  | .const .. => "constant"
  | .fvar .. => "free_variable"
  | .mvar .. => "metavariable"
  | .bvar .. => "bound_variable"
  | .app .. => "application"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .lit .. => "literal"
  | .sort .. => "sort"
  | .mdata .. => "metadata"
  | .proj .. => "projection"

def exprTypeText (e : Expr) : MetaM String := do
  try
    let ty ← inferType e
    return (← ppExpr ty).pretty 100
  catch _ =>
    return "<type unavailable>"

def constantRole (env : Environment) (n : Name) : String :=
  match lookup env n with
  | some (.thmInfo _) => "theorem"
  | some (.ctorInfo _) => "constructor"
  | some (.defnInfo _) => "definition"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some (.recInfo _) => "recursor"
  | some (.inductInfo _) => "inductive"
  | some (.quotInfo _) => "quotient"
  | none => "external_or_unresolved"

def expressionSummary (env : Environment) (e : Expr) : MetaM Json := do
  let e := e.consumeMData
  let ty ← exprTypeText e
  let mut fields := #[
    ("kind", Json.str (exprKindText e)),
    ("type", Json.str ty)]
  match e with
  | .const n ls =>
      fields := fields.push ("name", Json.str n.toString)
      fields := fields.push ("role", Json.str (constantRole env n))
      fields := fields.push ("universe_levels", Json.arr (ls.toArray.map fun l => Json.str (toString l)))
  | .fvar fid =>
      let d ← fid.getDecl
      fields := fields.push ("name", Json.str d.userName.toString)
      fields := fields.push ("role", Json.str "local_assumption")
      fields := fields.push ("binderInfo", Json.str (biText d.binderInfo))
  | .bvar i => fields := fields.push ("index", toJson i)
  | .lit l => fields := fields.push ("literal", Json.str (litText l))
  | _ => pure ()
  return Json.mkObj fields.toList

def headInfo (env : Environment) (e : Expr) : MetaM Json := do
  let e := e.consumeMData
  match e with
  | .const n ls => return Json.mkObj [
      ("kind", Json.str "constant"),
      ("name", Json.str n.toString),
      ("role", Json.str (constantRole env n)),
      ("universe_levels", Json.arr (ls.toArray.map (fun l => Json.str (toString l))))]
  | .fvar fid =>
      let d ← fid.getDecl
      let ty ← ppExpr d.type
      return Json.mkObj [
        ("kind", Json.str "free_variable"),
        ("name", Json.str d.userName.toString),
        ("role", Json.str "local_assumption"),
        ("binderInfo", Json.str (biText d.binderInfo)),
        ("type", Json.str (ty.pretty 100))]
  | _ =>
      return Json.mkObj [
        ("kind", Json.str (exprKindText e)),
        ("name", Json.null),
        ("role", Json.str "unsupported_head")]

def applicationRole (head : Expr) (headRole : String) (relevance : String) : String :=
  match head.consumeMData with
  | .fvar .. => "local_assumption_application"
  | .const .. =>
      if relevance == "proof_term" &&
          (headRole == "theorem" || headRole == "constructor" ||
            headRole == "opaque" || headRole == "axiom") then
        "proof_application"
      else if headRole == "definition" || headRole == "recursor" then
        "definition_application"
      else
        "constant_application"
  | _ => "unsupported_head_application"

def resultClass (outputType : Expr) (outputIsProposition : Bool) : MetaM String := do
  let whnfOutput ← try whnf outputType catch _ => pure outputType
  match whnfOutput.consumeMData with
  | .sort .zero => pure "proposition_value"
  | _ => pure (if outputIsProposition then "proof_term" else "data_value")

def isLocalDeclarationName (n : Name) : Bool :=
  (`Percolation).isPrefixOf n || (`BondPercolation).isPrefixOf n ||
    (`Solution).isPrefixOf n || (`Challenge).isPrefixOf n

def needsDetailedApplication (env : Environment) (head : Expr) : Bool :=
  match head.consumeMData with
  | .fvar .. => true
  | .const n _ =>
      if !isLocalDeclarationName n then
        false
      else
        let role := constantRole env n
        role == "theorem" || role == "constructor" || role == "opaque" || role == "axiom"
  | _ => false

def safeDefEq (a b : Expr) : MetaM (Option Bool) := do
  try
    return some (← isDefEq a b)
  catch _ =>
    return none

def applicationRecord (env : Environment) (path : String) (detailed : Bool) (e : Expr) : MetaM Json := do
  let e := e.consumeMData
  let head := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let headJson ← headInfo env head
  let base : List (String × Json) := [("path", Json.str path), ("head", headJson),
    ("arity", toJson args.size)]
  if !detailed then
    return Json.mkObj (base ++ [
      ("application_role", Json.str "structural_only_application"),
      ("proof_relevance", Json.str "structural_only"),
      ("result_class", Json.str "unknown"),
      ("detail_status", Json.str "structural_only_external"),
      ("arguments", Json.arr #[]),
      ("output_type", Json.null),
      ("output_is_proposition", Json.null),
      ("local_context", Json.null),
      ("status", Json.str "structural_only")])
  let headType ← exprTypeText head
  let mut currentType ← try
    inferType head
  catch _ =>
    pure (mkSort .zero)
  let mut mappings := #[]
  let mut unsupported := false
  for i in [0:args.size] do
    let arg := args[i]!
    let argSummary ← expressionSummary env arg
    let argType ← try inferType arg catch _ => pure (mkSort .zero)
    let actualTypeText ← exprTypeText arg
    let currentWhnf ← try whnf currentType catch _ => pure currentType
    match currentWhnf with
    | .forallE binderName domain body binderInfo =>
        let expectedText ← exprTypeText domain
        let expectedIsProp ← try isProp domain catch _ => pure false
        let defeq ← safeDefEq domain argType
        mappings := mappings.push <| Json.mkObj [
          ("index", toJson i),
          ("binderName", Json.str binderName.toString),
          ("binderInfo", Json.str (biText binderInfo)),
          ("expected_type", Json.str expectedText),
          ("expected_is_proposition", Json.bool expectedIsProp),
          ("actual_type", Json.str actualTypeText),
          ("definitional_type_match", match defeq with
            | some value => Json.bool value
            | none => Json.null),
          ("argument", argSummary)]
        currentType := body.instantiate1 arg
    | _ =>
        unsupported := true
        mappings := mappings.push <| Json.mkObj [
          ("index", toJson i),
          ("binderName", Json.null),
          ("binderInfo", Json.null),
          ("expected_type", Json.null),
          ("expected_is_proposition", Json.null),
          ("actual_type", Json.str actualTypeText),
          ("definitional_type_match", Json.null),
          ("argument", argSummary),
          ("mapping_status", Json.str "unsupported_nonforall_head_type")]
  let outputType ← try inferType e catch _ => pure (mkSort .zero)
  let outputText ← exprTypeText e
  let outputIsProp ← try isProp outputType catch _ => pure false
  let result ← resultClass outputType outputIsProp
  let headRole := match headJson.getObjVal? "role" with
    | .ok (.str role) => role
    | _ => "unsupported_head"
  let relevance := if result == "proof_term" then "proof_term" else "data_term"
  let role := applicationRole head headRole relevance
  let retainContext := result == "proof_term"
  let context ← if retainContext then localContextSnapshot else pure Json.null
  return Json.mkObj (base ++ [
    ("application_role", Json.str role),
    ("proof_relevance", Json.str relevance),
    ("result_class", Json.str result),
    ("head_type", Json.str headType),
    ("arguments", Json.arr mappings),
    ("output_type", Json.str outputText),
    ("output_is_proposition", Json.bool outputIsProp),
    ("local_context", context),
    ("context_status", Json.str (if retainContext then "exact_proof_context" else "omitted_data_context")),
    ("detail_status", Json.str "exact_context"),
    ("status", Json.str (if unsupported then "unsupported_parameter_shape" else "checked"))])

def referenceRecord (env : Environment) (path : String) (mode : String) (n : Name) : Json :=
  Json.mkObj [
    ("path", Json.str path),
    ("name", Json.str n.toString),
    ("role", Json.str (if mode == "type" then "type_only_reference" else "proof_constant_reference")),
    ("context", Json.str mode),
    ("declaration_role", Json.str (constantRole env n))]

def mergeJsonArrays (left right : Array Json) : Array Json := left ++ right

structure SubtermResult where
  applications : Array Json
  references : Array Json
  omittedStructuralApplications : Nat
  omittedExternalReferences : Nat

def mergeSubtermResults (left right : SubtermResult) : SubtermResult :=
  { applications := left.applications ++ right.applications
    references := left.references ++ right.references
    omittedStructuralApplications :=
      left.omittedStructuralApplications + right.omittedStructuralApplications
    omittedExternalReferences := left.omittedExternalReferences + right.omittedExternalReferences }

partial def collectSubterms (env : Environment) (path : String) (mode : String)
    (inAppFn compact : Bool) (e : Expr) : MetaM SubtermResult := do
  let e := e.consumeMData
  match e with
  | .const n _ =>
      if compact && !isLocalDeclarationName n then
        return SubtermResult.mk #[] #[] 0 1
      else
        return SubtermResult.mk #[] #[referenceRecord env path mode n] 0 0
  | .fvar .. | .bvar .. | .mvar .. | .lit .. | .sort .. =>
      return SubtermResult.mk #[] #[] 0 0
  | .app f a =>
      let detailed := needsDetailedApplication env e.getAppFn
      let mut applications := #[]
      unless inAppFn || (compact && !detailed) do
        applications := applications.push
          (← applicationRecord env path detailed e)
      let omittedApplications := if !inAppFn && compact && !detailed then 1 else 0
      let fnResult ← collectSubterms env (path ++ "/fn") mode true compact f
      let argResult ← collectSubterms env (path ++ "/arg") mode false compact a
      let ownResult := SubtermResult.mk applications #[] omittedApplications 0
      return mergeSubtermResults ownResult (mergeSubtermResults fnResult argResult)
  | .lam n ty body bi =>
      let typeResult ← collectSubterms env (path ++ "/type") "type" false compact ty
      let bodyResult ← withLocalDecl n bi ty fun fvar =>
        collectSubterms env (path ++ "/body") mode false compact (body.instantiate1 fvar)
      return mergeSubtermResults typeResult bodyResult
  | .forallE n ty body bi =>
      let typeResult ← collectSubterms env (path ++ "/type") "type" false compact ty
      let bodyResult ← withLocalDecl n bi ty fun fvar =>
        collectSubterms env (path ++ "/body") "type" false compact (body.instantiate1 fvar)
      return mergeSubtermResults typeResult bodyResult
  | .letE n ty value body nondep =>
      let typeResult ← collectSubterms env (path ++ "/type") "type" false compact ty
      let valueResult ← collectSubterms env (path ++ "/value") mode false compact value
      let bodyResult ← withLetDecl n ty value (nondep := nondep) fun fvar =>
        collectSubterms env (path ++ "/body") mode false compact (body.instantiate1 fvar)
      return mergeSubtermResults typeResult (mergeSubtermResults valueResult bodyResult)
  | .mdata _ body => collectSubterms env path mode inAppFn compact body
  | .proj _ _ body => collectSubterms env (path ++ "/body") mode false compact body

def roots : Array Name := #[`BondPercolation.percolation_continuity]

def sortNames (names : Array Name) : Array Name :=
  names.qsort (fun left right => left.toString < right.toString)

def localDependencies (env : Environment) (nm : Name) : Array Name :=
  match lookup env nm with
  | none => #[]
  | some ci =>
      match ci.value? (allowOpaque := true) with
      | none => #[]
      | some value =>
          sortNames <| (Expr.getUsedConstantsAsSet value).toList.toArray.filter
            isLocalDeclarationName

def traversalField (value : Option Name) : Json :=
  match value with
  | some nm => Json.str nm.toString
  | none => Json.null

def proofRecord (env : Environment) (nm : Name) (depth : Nat) (parent : Option Name)
    (includeTree compact : Bool) : MetaM Json :=
  match lookup env nm with
  | none => pure <| Json.mkObj [
      ("declaration", Json.str nm.toString),
      ("status", Json.str "missing_from_environment"),
      ("traversal_depth", toJson depth),
      ("discovered_from", traversalField parent),
      ("local_dependencies", Json.arr #[])]
  | some ci =>
      match ci.value? (allowOpaque := true) with
      | none => pure <| Json.mkObj [
          ("declaration", Json.str nm.toString),
          ("status", Json.str "no_value"),
          ("traversal_depth", toJson depth),
          ("discovered_from", traversalField parent),
          ("local_dependencies", Json.arr #[]),
          ("kind", Json.str (match ci with
            | .thmInfo _ => "theorem"
            | .defnInfo _ => "def"
            | .axiomInfo _ => "axiom"
            | .opaqueInfo _ => "opaque"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "ctor"
            | .recInfo _ => "rec"
            | .quotInfo _ => "quot"))]
      | some value => do
          let subterms ← collectSubterms env "" "proof" false compact value
          let dependencies := localDependencies env nm
          pure <| Json.mkObj [
            ("declaration", Json.str nm.toString),
            ("status", Json.str "captured"),
            ("traversal_depth", toJson depth),
            ("discovered_from", traversalField parent),
            ("local_dependencies", Json.arr (dependencies.map fun n => Json.str n.toString)),
            ("proof_constants", Json.arr (((Expr.getUsedConstantsAsSet value).toList.map
              fun n => Json.str n.toString).toArray)),
            ("application_records", Json.arr subterms.applications),
            ("reference_records", Json.arr subterms.references),
            ("omitted_structural_application_count", toJson subterms.omittedStructuralApplications),
            ("omitted_external_reference_count", toJson subterms.omittedExternalReferences),
            ("fuel", toJson treeFuel),
            ("tree", if includeTree then proofTree treeFuel value else Json.null),
            ("tree_status", Json.str (if includeTree then "captured" else "omitted_compact_full_cone"))]

def traversalItems (env : Environment) : CoreM (Array (Name × Nat × Option Name)) := do
  let mut queue : Array (Name × Nat × Option Name) :=
    roots.map fun nm => (nm, 0, none)
  let mut nextIndex := 0
  let mut visited : Std.HashSet Name := {}
  let mut items := #[]
  while nextIndex < queue.size do
    let item := queue[nextIndex]!
    nextIndex := nextIndex + 1
    let nm := item.1
    unless visited.contains nm do
      visited := visited.insert nm
      items := items.push item
      for dependency in localDependencies env nm do
        unless visited.contains dependency do
          queue := queue.push (dependency, item.2.1 + 1, some nm)
  pure items

def traversalManifest (items : Array (Name × Nat × Option Name)) : Json :=
  Json.mkObj [
    ("schema_version", toJson 1),
    ("algorithm", Json.str "deterministic breadth-first local proof-cone traversal"),
    ("root_declarations", Json.arr (roots.map fun n => Json.str n.toString)),
    ("record_count", toJson items.size),
    ("items", Json.arr <| items.map fun item => Json.mkObj [
      ("declaration", Json.str item.1.toString),
      ("traversal_depth", toJson item.2.1),
      ("discovered_from", traversalField item.2.2)])]

def maxTraversalDepth (items : Array (Name × Nat × Option Name)) : Nat :=
  items.foldl (init := 0) fun current item => max current item.2.1

def batchJson (env : Environment) (items : Array (Name × Nat × Option Name))
    (batchStart batchSize : Nat) (includeTrees compact : Bool) : MetaM Json := do
  let selectedItems := (items.toList.drop batchStart |>.take batchSize).toArray
  let mut records := #[]
  for item in selectedItems do
    records := records.push (← proofRecord env item.1 item.2.1 item.2.2 includeTrees compact)
  pure <| Json.mkObj [
    ("schema_version", toJson 1),
    ("generated_from", Json.str "Solution"),
    ("toolchain", Json.str s!"leanprover/lean4:v{Lean.versionString}"),
    ("mode", Json.str "batch"),
    ("batch_start", toJson batchStart),
    ("batch_size", toJson batchSize),
    ("global_record_count", toJson items.size),
    ("max_depth", toJson (maxTraversalDepth items)),
    ("items", Json.arr <| selectedItems.map fun item => Json.mkObj [
      ("declaration", Json.str item.1.toString),
      ("traversal_depth", toJson item.2.1),
      ("discovered_from", traversalField item.2.2)]),
    ("records", Json.arr records)]

unsafe def main : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `Percolation },
    { module := `Solution }] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<proof-trace>", fileMap := default, maxHeartbeats := 0 }
  let items ← traversalItems env |>.toIO' ctx { env }
  let mode ← IO.getEnv "XYLEM_TRACE_MODE"
  match mode with
  | some "manifest" =>
      let path := (← IO.getEnv "XYLEM_TRACE_MANIFEST").getD "/tmp/percolation-proof-cone-manifest.json"
      IO.FS.writeFile path (Json.compress (traversalManifest items))
  | some "batch" =>
      let start := ((← IO.getEnv "XYLEM_TRACE_BATCH_START").getD "0").toNat?.getD 0
      let size := ((← IO.getEnv "XYLEM_TRACE_BATCH_SIZE").getD "0").toNat?.getD 0
      let includeTrees := (← IO.getEnv "XYLEM_TRACE_INCLUDE_TREES").getD "0" == "1"
      let compact := (← IO.getEnv "XYLEM_TRACE_COMPACT").getD "1" == "1"
      let result ← (MetaM.run' (batchJson env items start size includeTrees compact)).toIO' ctx { env }
      IO.println (Json.compress result)
  | _ =>
      let includeTrees := (← IO.getEnv "XYLEM_TRACE_INCLUDE_TREES").getD "0" == "1"
      let compact := (← IO.getEnv "XYLEM_TRACE_COMPACT").getD "1" == "1"
      let result ← (MetaM.run' (batchJson env items 0 items.size includeTrees compact)).toIO' ctx { env }
      IO.println (Json.compress result)
  return 0
