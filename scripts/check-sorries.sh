#!/usr/bin/env bash
# Enforces the project's proof-hole policy: every `.lean` file under `GLang/`
# must be free of `sorry` and `admit` in code (docstring mentions are ignored).
# No new project axioms are permitted; the artifact contract audits axiom closures.
#
# Why: project-level `lake build` is permissive about `sorry` (it emits
# warnings, not errors). This script is the regression gate that
# catches accidental new sorries creeping into production proofs.
#
# Run from the project root: `bash scripts/check-sorries.sh`
# Exit code 0 = clean, 1 = unauthorized sorry found.
set -euo pipefail

cd "$(dirname "$0")/.."

# No anonymous proof holes are permitted. Named axioms are audited separately.
ALLOWED=()

is_allowed() {
  local cand="$1" allowed
  for allowed in "${ALLOWED[@]}"; do
    [ "$cand" = "$allowed" ] && return 0
  done
  return 1
}

# strip_noncode: read Lean source on stdin, emit each line with comments and
# string-literal contents removed. State is tracked across lines so words such
# as `sorry` used by report/QA code are not mistaken for proof commands.
strip_noncode() {
  awk '
    BEGIN { depth = 0; in_string = 0; escaped = 0 }
    {
      line = $0
      out = ""
      i = 1
      n = length(line)
      while (i <= n) {
        if (depth == 0 && in_string == 0) {
          # Look for "--" line comment or "/-" block start.
          c2 = substr(line, i, 2)
          if (c2 == "--") {
            # Rest of line is a comment.
            break
          } else if (c2 == "/-") {
            depth = 1
            i += 2
          } else if (substr(line, i, 1) == "\"") {
            in_string = 1
            escaped = 0
            i += 1
          } else {
            out = out substr(line, i, 1)
            i += 1
          }
        } else if (depth > 0) {
          # Inside a block comment; look for nested "/-" or closing "-/".
          c2 = substr(line, i, 2)
          if (c2 == "/-") {
            depth += 1
            i += 2
          } else if (c2 == "-/") {
            depth -= 1
            i += 2
          } else {
            i += 1
          }
        } else {
          # Inside a string.  Honor Lean escapes so an escaped quote does not
          # expose the rest of the literal as source code.
          ch = substr(line, i, 1)
          if (escaped == 1) {
            escaped = 0
          } else if (ch == "\\") {
            escaped = 1
          } else if (ch == "\"") {
            in_string = 0
          }
          i += 1
        }
      }
      print out
    }
  '
}

offenders=""
while IFS= read -r f; do
  if is_allowed "$f"; then continue; fi
  hits=$(strip_noncode < "$f" \
         | grep -nE '(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)' \
         || true)
  if [ -n "$hits" ]; then
    while IFS= read -r line; do
      offenders+="$f:$line"$'\n'
    done <<<"$hits"
  fi
done < <(find GLang -name '*.lean' -type f | sort)

if [ -n "$offenders" ]; then
  echo 'FAIL: anonymous Lean proof hole (`sorry` or `admit`) found.'
  echo
  echo "Allowed files (proof holes permitted):"
  for f in "${ALLOWED[@]}"; do echo "  - $f"; done
  echo
  echo "Offending lines (line numbers are post-comment-stripping; check the source):"
  printf '%s' "$offenders"
  echo
  echo "Prove the obligation. Do not add a project axiom or extend ALLOWED."
  exit 1
fi

echo 'OK: no anonymous Lean proof holes (`sorry` or `admit`) in GLang/.'
if [ "${#ALLOWED[@]}" -eq 0 ]; then
  echo "Allowed files: none"
else
  echo "Allowed files:"
  for f in "${ALLOWED[@]}"; do
    n=$(strip_noncode < "$f" \
        | grep -cE '(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)' \
        || true)
    echo "  - $f ($n occurrences in code)"
  done
fi
