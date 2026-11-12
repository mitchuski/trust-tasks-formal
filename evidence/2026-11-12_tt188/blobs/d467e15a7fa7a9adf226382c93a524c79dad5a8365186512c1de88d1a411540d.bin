#!/usr/bin/env sh
# Build every model, print each theorem's axiom footprint, and fail on
# anything beyond Lean's standard axioms, on sorry, or on a kernel replay
# failure. Usage: ./check.sh
set -eu
export NO_COLOR=1 CLICOLOR=0 TERM=dumb
cd "$(dirname "$0")"

lake build

out=$(lake env lean Checks.lean 2>&1) || true
printf '%s\n' "$out"

if printf '%s\n' "$out" | grep -qE '(^|: )error|sorryAx'; then
  echo "FAIL: error or sorry in Checks.lean" >&2; exit 1
fi
bad=$(printf '%s\n' "$out" | grep 'depends on axioms' \
  | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
if [ -n "$bad" ]; then
  echo "FAIL: non-standard axioms: $bad" >&2; exit 1
fi

# every theorem in TrustTasks/ is listed in Checks.lean
missing=0
for f in TrustTasks/*.lean; do
  for t in $(awk '/^\/-/{c=1} c&&/-\//{c=0;next} !c' "$f" | grep -oE '^theorem [A-Za-z0-9_.]+' | awk '{print $2}'); do
    grep -qE "\.$t\$" Checks.lean || { echo "not in Checks.lean: $f $t" >&2; missing=1; }
  done
done
[ "$missing" -eq 0 ] || { echo "FAIL: theorems missing from Checks.lean" >&2; exit 1; }

lake env leanchecker --fresh TrustTasks
echo "OK: $(printf '%s\n' "$out" | grep -c 'axioms') theorems, standard axioms only, leanchecker clean"
