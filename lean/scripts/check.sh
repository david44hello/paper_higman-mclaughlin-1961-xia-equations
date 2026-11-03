#!/usr/bin/env bash
# check.sh — builds the Xia project, then runs the source policy, the claim audit and (--final) the final gate.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
# Usage: bash scripts/check.sh            the work gate: no OPEN or VIOLATION row, no forbidden construct anywhere
#        bash scripts/check.sh --final    the final gate: placeholders only as the whole body of the rows listed in
#                                         OPEN_ROWS.txt (scripts/final_gate.py); those rows OPEN, every other row not
#        bash scripts/check.sh --test     self-test, no Lean
# `axiom` is forbidden everywhere (the Xia sources assume no cited results); backups in any versions/ folder are not
# scanned.  Conditional (PROVED GIVEN) and NOT FORMALIZED rows stay distinct from proof gaps.
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
statements=Xia/Paper/Statements.lean
forbidden='sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|debug[.]skipKernelTC|csimp'

require_commands() {
    local command_name
    for command_name in "$@"; do
        command -v "$command_name" >/dev/null || { echo "ERROR: '$command_name' is not on PATH (needed by $0)." >&2; return 2; }
    done
}

audit_has_gaps() {
    rg -q '[|] (OPEN|VIOLATION) [|]' "$1"
}

scan_sources() {
    local source_dir=$1 mode=$2 status=0 failed=0
    local -a final_skip=()
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    case "$mode" in
        work) ;;
        final) final_skip=(--glob "!$statements") ;;
        *) echo "ERROR: scan mode must be work or final: $mode" >&2; return 2 ;;
    esac
    # Deliberately conservative: forbidden words in comments/strings also fail.
    # Scan hidden/untracked Lean files too; dependencies, Git data, and backups in any versions/ folder are excluded.
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!**/versions/**' "${final_skip[@]}" "$forbidden" .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole, axiom or forbidden proof construct in local Lean sources.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    if [[ "$mode" == final ]]; then
        # Statements.lean: every forbidden word but the placeholder, whose placement final_gate.py checks.
        status=0
        (cd "$source_dir" && rg -n -w "${forbidden#sorry|}" "$statements") || status=$?
        if (( status == 0 )); then
            echo "ERROR: forbidden proof construct in $statements." >&2
            failed=1
        elif (( status != 1 )); then return "$status"; fi
    fi
    return "$failed"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import pathlib, shutil, sys; shutil.rmtree(pathlib.Path(sys.argv[1]))" "$fixture"' EXIT
    mkdir -p "$fixture/Xia/Paper/versions" "$fixture/Xia/Cited" "$fixture/.lake/packages/dependency" "$fixture/versions"
    printf 'theorem good : True := True.intro\n' > "$fixture/Xia/Basic.lean"
    printf 'theorem dependency_result : True := by sorry\n' > "$fixture/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/versions/Old.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/Xia/Paper/versions/Statements_version_0.1.lean"
    scan_sources "$fixture" work || return 1
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro'; do
        printf '%b\n' "$bad_source" > "$fixture/Xia/Basic.lean"
        if scan_sources "$fixture" work >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    printf 'theorem good : True := True.intro\n' > "$fixture/Xia/Basic.lean"
    # No cited inputs: an axiom fails in every folder, a Cited/ one included
    printf 'axiom external_result : True\n' > "$fixture/Xia/Cited/External.lean"
    if scan_sources "$fixture" work >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted an axiom in Xia/Cited.' >&2; return 1
    fi
    printf 'theorem fine : True := True.intro\n' > "$fixture/Xia/Cited/External.lean"
    # final mode: the placeholder may appear only in Statements.lean (final_gate.py then checks where)
    mkdir -p "$fixture/Xia/Proofs"
    printf 'theorem row_open : True := by\n  sorry\n' > "$fixture/$statements"
    scan_sources "$fixture" final || { echo 'TEST FAILED: final mode rejected a Statements placeholder.' >&2; return 1; }
    if scan_sources "$fixture" work >/dev/null 2>&1; then
        echo 'TEST FAILED: work mode accepted a Statements placeholder.' >&2; return 1
    fi
    printf 'theorem stray : True := by sorry\n' > "$fixture/Xia/Proofs/Stray.lean"
    if scan_sources "$fixture" final >/dev/null 2>&1; then
        echo 'TEST FAILED: final mode accepted a stray placeholder in Proofs.' >&2; return 1
    fi
    printf 'theorem fine : True := True.intro\n' > "$fixture/Xia/Proofs/Stray.lean"
    local statements_bad
    for statements_bad in 'theorem row_open : True := by\n  admit' 'axiom row_open : True'; do
        printf '%b\n' "$statements_bad" > "$fixture/$statements"
        if scan_sources "$fixture" final >/dev/null 2>&1; then
            echo "TEST FAILED: final mode accepted in Statements: $statements_bad" >&2; return 1
        fi
    done
    if scan_sources "$fixture" sloppy >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted an unknown scan mode.' >&2; return 1
    fi
    if scan_sources "$fixture/no-such-folder" work >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted a missing source folder.' >&2; return 1
    fi
    python3 "$project_dir/scripts/final_gate.py" --test >/dev/null || { echo 'TEST FAILED: final_gate.py --test' >&2; return 1; }
    printf '%s\n' '| # | Claim | Status |' '| 1 | good | PROVED |' '| 2 | given | PROVED GIVEN hX12, hX34b |' \
        '| 3 | n | NOT FORMALIZED |' > "$fixture/AUDIT.md"
    if audit_has_gaps "$fixture/AUDIT.md"; then
        echo 'TEST FAILED: clear audit rejected.' >&2; return 1
    fi
    local claim_status
    for claim_status in OPEN VIOLATION; do
        printf '| 1 | bad | %s |\n' "$claim_status" > "$fixture/AUDIT.md"
        audit_has_gaps "$fixture/AUDIT.md" || { echo "TEST FAILED: missed $claim_status" >&2; return 1; }
    done
    echo 'PASS: source policy and audit completeness accept valid inputs and reject forbidden/open inputs.'
)

main() {
    local mode
    case "${1:-}" in
        --test) [[ $# == 1 ]] || return 2; require_commands python3 rg; run_tests; return ;;
        --final) [[ $# == 1 ]] || return 2; mode=final ;;
        '') [[ $# == 0 ]] || return 2; mode=work ;;
        *) echo "Usage: $0 [--test | --final]   (no flag = the work gate)" >&2; return 2 ;;
    esac
    require_commands lake python3 rg
    cd "$project_dir"
    export LEAN_NUM_THREADS=1
    # Fail before the real build if Mathlib would need compilation (run `lake exe cache get` first).
    lake build --no-build mathlib/Mathlib
    lake build Xia
    local scan_status=0
    scan_sources . "$mode" || scan_status=$?
    python3 scripts/audit.py
    if [[ "$mode" == final ]]; then
        python3 scripts/final_gate.py "$statements" CLAIMS.json OPEN_ROWS.txt || return 1
        (( scan_status == 0 )) || return "$scan_status"
        echo 'PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.'
        return 0
    fi
    local audit_status=0
    audit_has_gaps AUDIT.md || audit_status=$?
    if (( audit_status == 0 )); then
        echo 'ERROR: incomplete or forbidden claim in final audit.' >&2
        return 1
    fi
    (( audit_status == 1 )) || return "$audit_status"
    (( scan_status == 0 )) || return "$scan_status"
    echo 'PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.'
}

main "$@"
