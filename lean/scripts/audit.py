#!/usr/bin/env python3
"""audit.py — the Xia claim audit: Lean's own `#print axioms` and declared signatures, row by row and per printed claim.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Usage: python3 scripts/audit.py          a `lake build --no-build` freshness check, then one `lake env lean` of the probe
       python3 scripts/audit.py --test   self-test, no Lean
Paths are relative to the project folder (the parent of scripts/).
Reads:  Xia/Paper/Statements.lean, the Xia sources (axiom scan), CLAIM_MAP.tsv (required).
Writes: AUDIT.md, CLAIMS.json (the same bytes on every run of the same tree);
        logs/audit_probe.lean, logs/audit_probe.log, logs/audit_built.log (logs/ is ignored by Git).
Row status, from Lean's output only:
  PROVED                  axioms within propext, Classical.choice, Quot.sound
  PROVED GIVEN <names>    PROVED, and the signature has binders named hX... (Xia's results entered as hypotheses)
  OPEN                    depends on sorryAx (and nothing non-standard besides)
  VIOLATION               any other axiom: the audit FAILS (after writing the reports)
Printed claims (CLAIM_MAP.tsv lines `id<TAB>description<TAB>REQUIRED<TAB>SUPPORT`, '#' comments; the map's own header):
  REQUIRED = alternatives separated by '|'; one alternative = comma-listed rows that must ALL hold, so its status is
  its worst row (OPEN if any row is OPEN, else PROVED GIVEN the union of the rows' hypotheses, else PROVED).
  Claim status = the best alternative (PROVED > PROVED GIVEN, fewer hypotheses first > OPEN). SUPPORT rows are listed
  only. Empty REQUIRED = NOT FORMALIZED. REQUIRED = PENDING (rows not yet stated) = OPEN.
  VIOLATION in any row the claim names = VIOLATION.
  A map row that is not a Statements theorem FAILS the audit; a theorem named by no claim is a WARNING.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent.parent
LIB = "Xia"
NAMESPACE = LIB + ".Paper"
STATEMENTS_PATH = LIB + "/Paper/Statements.lean"     # relative to PROJECT; also the name printed in the reports
STATEMENTS_MODULE = NAMESPACE + ".Statements"
CLAIM_MAP_PATH = "CLAIM_MAP.tsv"                       # relative to PROJECT
LOG_DIR = "logs"                                       # relative to PROJECT; ignored by Git
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
OPEN_AXIOM = "sorryAx"
HYP_PREFIX = "hX"
WORDS = ("PROVED", "PROVED GIVEN", "OPEN", "VIOLATION", "NOT FORMALIZED")   # display order of the totals
RANK = {"PROVED": 0, "PROVED GIVEN": 1, "OPEN": 2}                         # best first


def fail(message):
    raise SystemExit("AUDIT FAILED: " + message)


def warn(message):
    print("AUDIT WARNING: " + message, file=sys.stderr)


def read_input(path):
    """Text of a required input file; a missing file fails the audit."""
    if not path.is_file(): fail(f"missing input file: {path}")
    return path.read_text(encoding="utf-8")


def mask_comments(text):
    """Preserve offsets/newlines while removing nested Lean comments and strings."""
    chars = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                chars[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                chars[i:i+2] = "  "; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                if text[i] == '"': string = False
                i += 1
        elif text.startswith("/-", i):
            chars[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            chars[i:end] = " " * (end-i); i = end
        elif text[i] == '"':
            chars[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string:
        fail("unterminated comment/string")
    return "".join(chars)


def doc_first_line(text, offset):
    """First non-empty line of the docstring that directly precedes offset ('' if there is none)."""
    before = text[:offset].rstrip()
    start = before.rfind("/--")
    if not before.endswith("-/") or start < 0 or "-/" in before[start + 3:-2]:
        return ""
    lines = [line.strip() for line in before[start + 3:-2].splitlines() if line.strip()]
    return lines[0] if lines else ""


def parse_statements(text):
    """Plain, line-start theorem declarations, as required by the Statements contract."""
    clean = mask_comments(text)
    heads = list(re.finditer(r"^theorem\s+([A-Za-z_][\w']*)(?=\s)", clean, re.M))
    if len(heads) != len(re.findall(r"\btheorem\b", clean)):
        fail("unsupported theorem syntax; use plain line-start theorem declarations")
    if re.search(r"\b(?:lemma|example|axiom|opaque|def|abbrev|constant)\b", clean):
        fail("Statements may contain only theorem rows, imports, namespaces and registry comments")
    items = [{"name": head.group(1), "line": text.count("\n", 0, head.start()) + 1,
              "claim": doc_first_line(text, head.start())} for head in heads]
    names = [item["name"] for item in items]
    if not names or len(names) != len(set(names)):
        fail("empty or duplicate theorem inventory")
    return items


def parse_not_stated(text):
    """Entries `(Nx) reason` of the `/-! ## NOT stated ... -/` registry block(s); at least one block (it may be empty)."""
    blocks = re.findall(r"/-!\s*## NOT stated[^\n]*\n(.*?)-/", text, re.S)
    if not blocks: fail("need a /-! ## NOT stated registry block in Statements (empty is allowed)")
    body = "\n".join(blocks)
    items = [{"label": label, "reason": " ".join(reason.split()), "status": "NOT FORMALIZED"}
             for label, reason in re.findall(r"^\((N\w+)\)(.*?)(?=^\(N\w+\)|\Z)", body, re.S | re.M)]
    labels = [item["label"] for item in items]
    if len(labels) != len(set(labels)) or any(not item["reason"] for item in items):
        fail("empty reason or duplicate NOT stated label")
    return items


def is_backup(relative):
    return "versions" in Path(relative).parts


def lean_sources(tree):
    """{relative path: text} of the library's Lean sources; backups in any versions/ folder are not sources."""
    paths = [tree / (LIB + ".lean"), *sorted((tree / LIB).rglob("*.lean"))]
    return {str(path.relative_to(tree)): read_input(path)
            for path in paths if not is_backup(path.relative_to(tree))}


def axiom_declarations(sources):
    """'file:line' of every `axiom` keyword outside comments and strings. The Xia sources declare no axioms at all."""
    return [f"{name}:{text.count(chr(10), 0, match.start()) + 1}" for name, text in sources.items()
            for match in re.finditer(r"\baxiom\b", mask_comments(text))]


def row_list(field):
    return [row.strip().removeprefix(NAMESPACE + ".") for row in field.split(",") if row.strip()]


def parse_claim_line(number, line):
    fields = line.split("\t")
    if len(fields) != 4:
        fail(f"claim map line {number}: need 4 tab-separated fields (id, description, REQUIRED, SUPPORT), got {len(fields)}")
    pending = fields[2].strip() == "PENDING"   # rows not yet stated: the claim counts as OPEN
    required = [] if pending else ([row_list(alternative) for alternative in fields[2].split("|")] if fields[2].strip() else [])
    if any(not alternative for alternative in required): fail(f"claim map line {number}: empty REQUIRED alternative")
    return {"id": fields[0].strip(), "description": fields[1].strip(), "required": required, "pending": pending,
            "support": row_list(fields[3]), "line": number}


def named_rows(claim):
    return [row for alternative in claim["required"] for row in alternative] + claim["support"]


def parse_claim_map(text, names):
    """The claim lines (see the module docstring). Returns (claims, Statements theorems named by no claim)."""
    claims = [parse_claim_line(number, line) for number, line in enumerate(text.splitlines(), 1)
              if line.strip() and not line.lstrip().startswith("#")]
    ids = [claim["id"] for claim in claims]
    if not claims or "" in ids or len(ids) != len(set(ids)): fail("claim map: empty, blank or duplicate claim ids")
    named = {row for claim in claims for row in named_rows(claim)}
    unknown = sorted(named - set(names))
    if unknown: fail("claim map rows that are not Statements theorems: " + ", ".join(unknown))
    return claims, [name for name in names if name not in named]


def probe_text(names):
    lines = ["-- Generated by scripts/audit.py; do not edit. Compiled by scripts/audit.py with `lake env lean`.",
             f"import {STATEMENTS_MODULE}", "import Lean", "open Lean Elab Command", "",
             "/-- Binder names of the Pi spine of a declared type, outermost first; definitions are NOT unfolded. -/",
             "partial def xiaAuditPiNames : Expr → List Name",
             "  | .forallE name _ body _ => name :: xiaAuditPiNames body",
             "  | .mdata _ inner => xiaAuditPiNames inner",
             "  | _ => []", "",
             "/-- Prints `XIABINDERS|<row>|<signature binder names, comma-separated>|END`. -/",
             "def xiaAuditBinders (decl : Name) (row : String) : CommandElabM Unit := do",
             "  let info ← getConstInfo decl",
             '  let names := (xiaAuditPiNames info.type).map (·.eraseMacroScopes.toString)',
             '  logInfo m!"XIABINDERS|{row}|{",".intercalate names}|END"', ""]
    for name in names:
        lines += [f"#print axioms {NAMESPACE}.{name}", f'run_cmd xiaAuditBinders ``{NAMESPACE}.{name} "{name}"']
    return "\n".join(lines) + "\n"


def run_lake(arguments, log):
    """`lake <arguments>` in PROJECT, one Lean thread; stdout+stderr go to the log. Returns (returncode, output)."""
    try:
        proc = subprocess.run(["lake", *arguments], cwd=PROJECT, env=dict(os.environ, LEAN_NUM_THREADS="1"),
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    except FileNotFoundError:
        fail("`lake` is not on PATH (install Lean: https://lean-lang.org/install/)")
    (PROJECT / log).write_text(proc.stdout, encoding="utf-8")
    return proc.returncode, proc.stdout


def check_built(log):
    """Lake's own hash-based check (builds nothing): the oleans the probe imports must match the current sources."""
    returncode, _ = run_lake(["build", "--no-build", STATEMENTS_MODULE], log)
    if returncode:
        fail(f"{STATEMENTS_MODULE} is not built from the current sources (lake build --no-build rc {returncode}; "
             f"see {log}). Build it first: lake build {LIB}")


def run_probe(names):
    probe, log = f"{LOG_DIR}/audit_probe.lean", f"{LOG_DIR}/audit_probe.log"
    (PROJECT / probe).write_text(probe_text(names), encoding="utf-8")
    returncode, output = run_lake(["env", "lean", "-j1", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", probe],
                                  log)
    if returncode: fail(f"Lean failed on the probe (rc {returncode}); see {log}\n" + output[-3000:])
    return output


def parse_axioms(output, names):
    result = {}
    for match in re.finditer(r"'([\w.']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", output, re.S):
        if not match.group(1).startswith(NAMESPACE + "."): continue
        name = match.group(1).removeprefix(NAMESPACE + ".")
        if name in result: fail("duplicate axiom output for " + name)
        result[name] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
    if set(names) != set(result): fail("missing/unexpected axiom rows: " + str(set(names) ^ set(result)))
    return result


def parse_hypotheses(output, names):
    """Signature binders named hX..., in signature order, from the probe's XIABINDERS lines."""
    result = {}
    for match in re.finditer(r"XIABINDERS\|([^|\n]+)\|([^|\n]*)\|END", output):
        name, binders = match.groups()
        if name in result: fail("duplicate binder inspection for " + name)
        result[name] = [binder for binder in binders.split(",") if binder.startswith(HYP_PREFIX)]
    if set(names) != set(result): fail("missing/unexpected binder inspections: " + str(set(names) ^ set(result)))
    return result


def classify(axioms, hypotheses):
    if axioms - STANDARD - {OPEN_AXIOM}: return "VIOLATION"
    if OPEN_AXIOM in axioms: return "OPEN"
    return "PROVED GIVEN " + ", ".join(hypotheses) if hypotheses else "PROVED"


def status_word(status):
    return "PROVED GIVEN" if status.startswith("PROVED GIVEN ") else status


def alternative_status(rows):
    """All rows of one REQUIRED alternative must hold: (status, hypotheses) of its worst row, hypotheses united."""
    if any(row["status"] == "OPEN" for row in rows): return "OPEN", []
    hypotheses = list(dict.fromkeys(name for row in rows for name in row["xia_hypotheses"]))
    return ("PROVED GIVEN " + ", ".join(hypotheses) if hypotheses else "PROVED"), hypotheses


def claim_status(claim, rows_by_name):
    """(status, best REQUIRED alternative) of one printed claim."""
    if any(rows_by_name[name]["status"] == "VIOLATION" for name in named_rows(claim)): return "VIOLATION", []
    if claim.get("pending"): return "OPEN", []
    if not claim["required"]: return "NOT FORMALIZED", []
    options = [(alternative_status([rows_by_name[name] for name in alternative]), alternative)
               for alternative in claim["required"]]
    (status, _), best = min(options, key=lambda option: (RANK[status_word(option[0][0])], len(option[0][1])))
    return status, best


def count_words(statuses):
    counts = {word: 0 for word in WORDS}
    for status in statuses: counts[status_word(status)] += 1
    return counts


def totals_line(label, counts):
    shown = [f"{word} {counts[word]}" for word in WORDS if counts[word] or word != "NOT FORMALIZED"]
    return f"{label}: {sum(counts.values())} — " + ", ".join(shown) + "."


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def render_rows(rows):
    table = ["| # | Lean name | Paper claim | Status |", "|---|---|---|---|"]
    table += [f'| {i} | `{row["name"]}` | {cell(row["claim"] or "(NO DOCSTRING)")} | {cell(row["status"])} |'
              for i, row in enumerate(rows, 1)]
    return table


def render_printed(printed, uncovered):
    table = ["| Claim | Description | Status | Best alternative | REQUIRED (alternatives) | SUPPORT |",
             "|---|---|---|---|---|---|"]
    table += [f'| {cell(claim["id"])} | {cell(claim["description"])} | {cell(claim["status"])} | '
              f'{cell(", ".join(claim["best_alternative"]) or "—")} | '
              f'{cell(" | ".join(", ".join(alternative) for alternative in claim["required"]) or "—")} | '
              f'{cell(", ".join(claim["support"]) or "—")} |' for claim in printed]
    if uncovered:
        table += ["", f"WARNING: {len(uncovered)} Statements theorem(s) in no printed claim: "
                  + ", ".join(f"`{name}`" for name in uncovered)]
    return table


def render(rows, printed, uncovered, omitted):
    """AUDIT.md: a function of its inputs only (no dates, no absolute paths), so a rerun gives the same bytes."""
    text = [f"# {LIB} claim audit", "",
            "Generated by scripts/audit.py from Lean's `#print axioms` output and declared signatures "
            f"of `{STATEMENTS_PATH}`.", "",
            totals_line("Rows", count_words(row["status"] for row in rows)), "",
            "PROVED = only propext, Classical.choice, Quot.sound. PROVED GIVEN <names> = PROVED, with Xia's results "
            "entered as the named explicit hypotheses (signature binders hX...). OPEN = depends on sorryAx. "
            "VIOLATION = any other axiom (the audit fails). Semantic fidelity to the paper is NOT checked here.", "",
            "## Rows (Statements theorems)", "", *render_rows(rows), "", "## Per printed claim", "",
            totals_line("Printed claims", count_words(claim["status"] for claim in printed)), "",
            f"From `{CLAIM_MAP_PATH}`. Status = the best REQUIRED alternative; an alternative is as good as its "
            "worst row (hypotheses of its rows united). SUPPORT rows do not change the status. "
            "Empty REQUIRED = NOT FORMALIZED.", "",
            *render_printed(printed, uncovered), ""]
    text += ["## NOT stated in Lean (registry in Statements)", "", f"{len(omitted)} entries (not proved theorems).", "",
             "| Label | Reason and paper location |", "|---|---|"]
    text += [f'| {item["label"]} | {cell(item["reason"])} |' for item in omitted]
    return "\n".join(text) + "\n"


def read_claim_map(path, names):
    """The claim map is a required input: a missing map fails the audit."""
    return parse_claim_map(read_input(path), names)


def build_rows(items, axioms, hypotheses):
    return [dict(item, qualified_name=NAMESPACE + "." + item["name"], axioms=sorted(axioms[item["name"]]),
                 xia_hypotheses=hypotheses[item["name"]],
                 status=classify(axioms[item["name"]], hypotheses[item["name"]])) for item in items]


def build_printed(claims, rows):
    rows_by_name = {row["name"]: row for row in rows}
    printed = []
    for claim in claims:
        status, best = claim_status(claim, rows_by_name)
        printed.append(dict(claim, status=status, best_alternative=best))
    return printed


def claims_json(rows, printed, uncovered, omitted):
    """CLAIMS.json text: a function of its inputs only, like AUDIT.md."""
    data = {"project": "010", "namespace": NAMESPACE, "statements": STATEMENTS_PATH,
            "counts": count_words(row["status"] for row in rows), "claims": rows, "not_stated": omitted,
            "claim_map": CLAIM_MAP_PATH, "printed_claim_counts": count_words(c["status"] for c in printed),
            "printed_claims": printed, "rows_in_no_claim": uncovered}
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def write_reports(rows, printed, uncovered, omitted):
    (PROJECT / "AUDIT.md").write_text(render(rows, printed, uncovered, omitted), encoding="utf-8")
    (PROJECT / "CLAIMS.json").write_text(claims_json(rows, printed, uncovered, omitted), encoding="utf-8")


def report_to_stdout(rows, printed, uncovered):
    print(totals_line("AUDIT rows", count_words(row["status"] for row in rows)))
    for row in rows:
        if not row["claim"]: warn(f"row {row['name']} (Statements l.{row['line']}) has no docstring")
    print(totals_line("AUDIT printed claims", count_words(claim["status"] for claim in printed)))
    print("\n".join(render_printed(printed, [])))
    if uncovered: warn(f"{len(uncovered)} Statements theorem(s) in no printed claim: " + ", ".join(uncovered))
    print("wrote AUDIT.md and CLAIMS.json")


def main_audit():
    statements = PROJECT / STATEMENTS_PATH
    text = read_input(statements)
    items, omitted = parse_statements(text), parse_not_stated(text)
    names = [item["name"] for item in items]
    declared = axiom_declarations(lean_sources(PROJECT))
    if declared: fail("axiom declarations in the Xia sources (none are allowed): " + ", ".join(declared))
    claims, uncovered = read_claim_map(PROJECT / CLAIM_MAP_PATH, names)
    (PROJECT / LOG_DIR).mkdir(exist_ok=True)
    check_built(f"{LOG_DIR}/audit_built.log")
    output = run_probe(names)
    if read_input(statements) != text:
        fail(f"{STATEMENTS_PATH} changed during the audit (rows and docstrings may not match the probed oleans); rerun")
    rows = build_rows(items, parse_axioms(output, names), parse_hypotheses(output, names))
    printed = build_printed(claims, rows)
    write_reports(rows, printed, uncovered, omitted)
    report_to_stdout(rows, printed, uncovered)
    bad = [row["name"] for row in rows if row["status"] == "VIOLATION"]
    if bad: fail("VIOLATION rows (non-standard axioms): " + ", ".join(bad))


def expect_fail(function, *args):
    try: function(*args)
    except SystemExit: return
    raise AssertionError(f"{function.__name__} accepted bad input {args!r}")


def test_statements():
    sample = ("/-- Row 1 — Lemma 2.2 | first line.\nsecond line. -/\ntheorem foo' (hX12 : True) : True := by trivial\n"
              "/-- Row 2 — one line -/\ntheorem bar : True := by\n  sorry\n/-! section -/\ntheorem nodoc : True := trivial\n"
              "/-! ## NOT stated in Lean (with reasons) — wave 1\n(N1) Thm 2.1 (x.tex:9): cited;\n     no library.\n"
              "(N2) Rem 2.5: no claim.\n-/\nend Xia.Paper\n")
    rows = parse_statements(sample)
    assert [r["name"] for r in rows] == ["foo'", "bar", "nodoc"] and rows[1]["line"] == 5
    assert [r["claim"] for r in rows] == ["Row 1 — Lemma 2.2 | first line.", "Row 2 — one line", ""]
    omitted = parse_not_stated(sample)
    assert [o["label"] for o in omitted] == ["N1", "N2"] and omitted[0]["reason"] == "Thm 2.1 (x.tex:9): cited; no library."
    expect_fail(parse_not_stated, "no registry")
    expect_fail(parse_not_stated, "/-! ## NOT stated\n(N1) a\n(N1) b\n-/")
    for bad in ["theorem a : True := trivial\n theorem hidden : True := trivial", "lemma hidden : True := trivial",
                "theorem a : True := trivial\naxiom b : True", "theorem a : True := trivial\ntheorem a : True := trivial"]:
        expect_fail(parse_statements, bad)
    assert "theorem" not in mask_comments('/- outer /- theorem -/ more -/ "theorem"')
    return rows, omitted


def test_sources():
    assert is_backup("Xia/Paper/versions/Statements_version_0.71.lean") and is_backup("versions/a.lean")
    assert not is_backup("Xia/Paper/Statements.lean")
    sources = {"Xia/A.lean": "-- an axiom here is a comment\n/-- axiom -/\ntheorem t : True := trivial\n",
               "Xia/B.lean": 'def s := "axiom"\n\nprivate axiom evil : False\n'}
    assert axiom_declarations(sources) == ["Xia/B.lean:3"]
    expect_fail(read_input, PROJECT / "no-such-input.lean")


def test_lean_output(names):
    out = ("'Xia.Paper.foo'' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
           "'Xia.Paper.bar' depends on axioms: [propext, sorryAx]\n'Xia.Paper.nodoc' does not depend on any axioms\n"
           "XIABINDERS|foo'|hX12,h,hXia35|END\nXIABINDERS|bar|hX9|END\nXIABINDERS|nodoc||END\n")
    axioms, hyps = parse_axioms(out, names), parse_hypotheses(out, names)
    assert hyps == {"foo'": ["hX12", "hXia35"], "bar": ["hX9"], "nodoc": []}
    statuses = [classify(axioms[n], hyps[n]) for n in names]
    assert statuses == ["PROVED GIVEN hX12, hXia35", "OPEN", "PROVED"]
    for bad in ({"evil"}, {"evil", "sorryAx"}, {"Lean.ofReduceBool", "propext"}):
        assert classify(bad, []) == "VIOLATION"
    expect_fail(parse_axioms, out.replace("'Xia.Paper.bar'", "'Xia.Paper.other'"), names)
    expect_fail(parse_hypotheses, out + "XIABINDERS|bar||END\n", names)
    return axioms, hyps


def test_claim_map(names):
    tsv = ("# id\tdescription\tREQUIRED\tSUPPORT\n\nLem 2.2\tfourth power\tfoo', Xia.Paper.bar | foo'\t\n"
           "Thm 3.1\tcount\tbar\tfoo'\nRem 2.5\tanalogy (N2)\t\t\n")
    claims, uncovered = parse_claim_map(tsv, names)
    assert [c["required"] for c in claims] == [[["foo'", "bar"], ["foo'"]], [["bar"]], []]
    assert [c["support"] for c in claims] == [[], ["foo'"], []] and uncovered == ["nodoc"]
    for bad in ["X\tdesc\tnot_a_row\t\n", "X\tdesc\tbar\n", "X\td\tbar\t\nX\td\tfoo'\t\n", "# only comments\n",
                "X\td\tbar |\t\n", "X\td\tbar\tghost\n"]:
        expect_fail(parse_claim_map, bad, names)
    pending, _ = parse_claim_map("P\tnot yet stated\tPENDING\t\n", names)
    assert pending[0]["pending"] and pending[0]["required"] == []
    expect_fail(read_claim_map, PROJECT / "no-such-claim-map.tsv", names)   # the claim map is required
    return claims


def test_best_status():
    def row(name, status, hyps=()): return {"name": name, "status": status, "xia_hypotheses": list(hyps)}
    def claim(required, support=(), pending=False): return {"required": required, "support": list(support),
                                                            "pending": pending}
    rows = {r["name"]: r for r in [row("a", "PROVED GIVEN hX1, hX2", ["hX1", "hX2"]), row("b", "PROVED GIVEN hX1", ["hX1"]),
                                   row("e", "PROVED GIVEN hX3", ["hX3"]), row("c", "OPEN", ["hX9"]), row("d", "PROVED"),
                                   row("v", "VIOLATION")]}
    assert claim_status(claim([["a"], ["b"], ["c"]]), rows) == ("PROVED GIVEN hX1", ["b"])   # fewer hypotheses first
    assert claim_status(claim([["c"], ["a"], ["d"]]), rows) == ("PROVED", ["d"])
    assert claim_status(claim([["c"]]), rows) == ("OPEN", ["c"])
    assert claim_status(claim([["d", "c"]]), rows) == ("OPEN", ["d", "c"])                    # worst row of an alternative
    assert claim_status(claim([["b", "e"]]), rows) == ("PROVED GIVEN hX1, hX3", ["b", "e"])   # hypotheses united
    assert claim_status(claim([["d", "b"], ["a"]]), rows) == ("PROVED GIVEN hX1", ["d", "b"])
    assert claim_status(claim([["d"]], ["v"]), rows) == ("VIOLATION", [])                    # even in SUPPORT
    assert claim_status(claim([], ["d"]), rows) == ("NOT FORMALIZED", [])
    assert claim_status(claim([], ["d"], pending=True), rows) == ("OPEN", [])                # PENDING = OPEN


def test_render_and_probe(items, axioms, hyps, claims, omitted):
    rows = build_rows(items, axioms, hyps)
    printed = build_printed(claims, rows)
    assert [c["status"] for c in printed] == ["PROVED GIVEN hX12, hXia35", "OPEN", "NOT FORMALIZED"]
    report = render(rows, printed, ["nodoc"], omitted)
    assert "Lemma 2.2 \\| first line." in report and "(NO DOCSTRING)" in report and "`nodoc`" in report
    assert "foo', bar \\| foo'" in report
    assert "Rows: 3 — PROVED 1, PROVED GIVEN 1, OPEN 1, VIOLATION 0." in report
    assert "Printed claims: 3 — PROVED 0, PROVED GIVEN 1, OPEN 1, VIOLATION 0, NOT FORMALIZED 1." in report
    # the committed reports are deterministic: no absolute paths, and the same inputs give the same bytes
    data = claims_json(rows, printed, ["nodoc"], omitted)
    for text in (report, data):
        assert str(PROJECT) not in text and f"`{STATEMENTS_PATH}`" in report and f"`{CLAIM_MAP_PATH}`" in report
    assert report == render(rows, printed, ["nodoc"], omitted) and data == claims_json(rows, printed, ["nodoc"], omitted)
    assert json.loads(data)["statements"] == STATEMENTS_PATH and json.loads(data)["claim_map"] == CLAIM_MAP_PATH
    probe = probe_text([item["name"] for item in items])
    assert f"import {STATEMENTS_MODULE}" in probe and "#print axioms Xia.Paper.foo'" in probe
    assert 'run_cmd xiaAuditBinders ``Xia.Paper.nodoc "nodoc"' in probe
    # check.sh scans every .lean file of the tree for these words; the probe must never trip it
    assert not re.search(r"\b(?:sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|csimp)\b", probe)


def main_test():
    items, omitted = test_statements()
    names = [item["name"] for item in items]
    test_sources()
    axioms, hyps = test_lean_output(names)
    claims = test_claim_map(names)
    test_best_status()
    test_render_and_probe(items, axioms, hyps, claims, omitted)
    print("PASS: audit.py --test (statements, registry, axiom scan, Lean output, statuses, claim map, best status, "
          "Markdown, probe)")


def main():
    if sys.argv[1:] == ["--test"]: main_test()
    elif not sys.argv[1:]: main_audit()
    else: fail("usage: scripts/audit.py [--test]")


if __name__ == "__main__":
    main()
