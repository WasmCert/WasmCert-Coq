#!/bin/bash
set -euo pipefail

folder="${1:-./wast_testsuite}"
filter="${2:-}"
jobs="${JOBS:-$(nproc)}"

shopt -s nullglob

if [[ -n "$filter" ]]; then
  files=( "$folder"/*"$filter"*.wast )
else
  files=( "$folder"/*.wast )
fi

if (( ${#files[@]} == 0 )); then
  echo "No matching .wast files in '$folder'${filter:+ containing '$filter'}." >&2
  exit 1
fi

exe="${EXE:-_build/default/src/wasm_coq_interpreter.exe}"
if [[ ! -x "$exe" ]]; then
  dune build
fi

results_dir=$(mktemp -d)
lockfile="$results_dir/.lock"
: > "$lockfile"
trap 'rm -rf "$results_dir"' EXIT

# Worker function: run one .wast file, print output, write "passed total" to a result file.
# Output is grouped per-file under flock so parallel jobs don't interleave their reports.
run_one() {
  local wastfile="$1"
  local exe="$2"
  local results_dir="$3"
  local lockfile="$4"
  local base
  base=$(basename "$wastfile")

  # Announce job start (single-line, serialized).
  {
    flock 9
    echo ">>> Starting job: $base"
  } 9>"$lockfile"

  local output rc=0
  output=$("$exe" --wast "$wastfile" 2>&1) || rc=$?

  # Strip ANSI codes and CR in one pass for parsing.
  local cleaned
  cleaned=$(printf '%s' "$output" | tr -d '\r' | sed 's/\x1b\[[0-9;]*m//g')

  # Determine outcome and per-file result line.
  local summary
  if (( rc != 0 )); then
    summary="CRASH: $base"
    echo "0 0" > "$results_dir/$base"
  else
    local result_line
    if result_line=$(printf '%s' "$cleaned" | grep -m1 "Result: "); then
      if [[ "$result_line" =~ Result:\ ([0-9]+)/([0-9]+) ]]; then
        echo "${BASH_REMATCH[1]} ${BASH_REMATCH[2]}" > "$results_dir/$base"
        summary="DONE: $base — $result_line"
      else
        summary="PARSE ERROR: $base — could not parse result line"
        echo "0 0" > "$results_dir/$base"
      fi
    else
      summary="NO RESULT: $base"
      echo "0 0" > "$results_dir/$base"
    fi
  fi

  # Emit the full report as one atomic block, headed and tailed with the file name.
  {
    flock 9
    echo "===== Report: $base ====="
    echo "$output"
    echo "----- $summary -----"
    echo
  } 9>"$lockfile"
}
export -f run_one

echo "Running ${#files[@]} .wast files with $jobs parallel jobs..."

printf '%s\n' "${files[@]}" | xargs -P "$jobs" -I {} bash -c 'run_one "$@"' _ {} "$exe" "$results_dir" "$lockfile"

# Aggregate results
total_passed=0
total_tests=0
for f in "$results_dir"/*; do
  read -r p t < "$f"
  total_passed=$((total_passed + p))
  total_tests=$((total_tests + t))
done

echo "================"
if (( total_tests == 0 )); then
  echo "No tests run." >&2
  exit 1
fi

percentage=$(awk "BEGIN { printf \"%.2f\", ($total_passed / $total_tests) * 100 }")
echo "Total Passed: $total_passed/$total_tests ($percentage%)"

if (( total_passed < total_tests )); then
  echo "FAILED: $((total_tests - total_passed)) test(s) did not pass."
  exit 1
fi
