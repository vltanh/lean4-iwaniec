module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`): every module of `PaperName/`
-- (`Basic/`, `External/` and the paper's library) and the paper's Solution in `palomar/`, but no
-- Challenge, which holds a copy of the paper's definitions under the library's names. Generate the
-- lines with
--   { find PaperName -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- With several papers (references/multi-paper.md), `find ProjectName` in place of `find PaperName`
-- lists every paper's modules and `Common/`, and the second `find` every paper's Solution.
import all Agazzi.Basic.Analysis.Calculus.GradientConstraint
import all Agazzi.Basic.Analysis.Calculus.Lem4Lipschitz
import all Agazzi.Basic.Analysis.Calculus.Periodic
import all Agazzi.Basic.Analysis.Convex.SupportFunction
import all Agazzi.Basic.MeasureTheory.Lem4Periodic
import all Agazzi.Basic.Topology.MetricSpace.Lem4Periodize
import all Agazzi.Bridges
import all Agazzi.Corollary2.Norm
import all Agazzi.Corollary2.Quasiconvexity
import all Agazzi.Corollary2.Torus
import all Agazzi.Defs
import all Agazzi.External.BaernsteinMontgomerySmith.Basic
import all Agazzi.External.KinderlehrerStampacchia.Projection
import all Agazzi.External.Lehto.LowerBound
import all Agazzi.External.Lehto.TestFunctions
import all Agazzi.Proof.RowRepresentation
import all Agazzi.Proof.ScalarProjection.Defs
import all Agazzi.Proof.ScalarProjection.Existence
import all Agazzi.Proof.ScalarProjection.Main
import all Agazzi.Quasiconvex
import all Agazzi.Solution
import all Agazzi.Theorem1

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`External/`) that it uses, whether proved there or, in a conditional formalization,
assumed as hypotheses of its statement. It then checks every declaration of the library and the
theorems that Palomar's comparator checks. The run fails if any of them depends on an axiom other
than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a `sorry` shows up as the
axiom `sorryAx`). Its table of results is the source of the report's dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set `isLibraryModule`:
with one paper, every module under the root `PaperName` but the Challenge; with several, the root
`ProjectName` and each paper's Solution module.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `External/` or, when
general, in `Basic/`, and, in a conditional formalization, the propositions assumed as hypotheses.
The traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("KS I.2.1", ``External.KinderlehrerStampacchia.lemma2_1),
   ("KS I.2.3", ``External.KinderlehrerStampacchia.theorem2_3),
   ("BMS (1.2a)", ``External.BaernsteinMontgomerySmith.equation1_2a),
   ("BMS (1.2b)", ``External.BaernsteinMontgomerySmith.equation1_2b),
   ("BMS/Bu3 ineq.", ``External.BaernsteinMontgomerySmith.phi_le),
   ("Lehto", ``External.Lehto.lowerBound)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Thm 1", ``Agazzi.theorem1),
   ("Thm 1 (Lipschitz)", ``Agazzi.theorem1_lipschitz),
   ("Cor 2 (a)", ``Agazzi.corollary2),
   ("Cor 2 (a, Lipschitz)", ``Agazzi.corollary2_lipschitz),
   ("Cor 2 (b)", ``Agazzi.corollary2_norm),
   ("Lemma 3", ``Agazzi.lemma3),
   ("Lemma 4", ``Agazzi.lemma4)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of
`palomar/PaperName/comparator.json`), as the Solution restates them. -/
meta def solutionResults : List Name :=
  [``AgazziChallenge.det_eq, ``AgazziChallenge.opNorm_eq, ``AgazziChallenge.volume_unitSquare,
   ``AgazziChallenge.beurling_dzbar, ``AgazziChallenge.theorem1, ``AgazziChallenge.corollary2,
   ``AgazziChallenge.corollary2_norm, ``AgazziChallenge.pStar_sub_one_of_le_two,
   ``AgazziChallenge.pStar_sub_one_of_two_le]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: under the root `PaperName` (`Basic/`, `External/`,
the paper's library and the Solution), but not the Challenge. With several papers, under the root
`ProjectName` or a paper's Solution:
`` (`ProjectName).isPrefixOf m || [`PaperA.Solution, `PaperB.Solution].contains m ``. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`Agazzi).isPrefixOf m && m != `Agazzi.Challenge

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
