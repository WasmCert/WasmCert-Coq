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
  echo "No matching .wast files in '$folder'${filter:+ containing '$filter'}."
  exit 0
fi

dune build
exe="_build/default/src/wasm_coq_interpreter.exe"

results_dir=$(mktemp -d)
trap 'rm -rf "$results_dir"' EXIT

# Worker function: run one .wast file, print output, write "passed total" to a result file.
run_one() {
  local wastfile="$1"
  local exe="$2"
  local results_dir="$3"
  local base
  base=$(basename "$wastfile")

  echo "Running: $wastfile"

  local output
  if ! output=$("$exe" --wast "$wastfile" 2>&1); then
    echo "$output"
    echo "CRASH: $wastfile"
    echo "0 0" > "$results_dir/$base"
    return
  fi

  echo "$output"

  # Strip ANSI codes and CR in one pass
  local cleaned
  cleaned=$(printf '%s' "$output" | tr -d '\r' | sed 's/\x1b\[[0-9;]*m//g')

  local result_line
  if result_line=$(printf '%s' "$cleaned" | grep -m1 "Result: "); then
    if [[ "$result_line" =~ Result:\ ([0-9]+)/([0-9]+) ]]; then
      echo "${BASH_REMATCH[1]} ${BASH_REMATCH[2]}" > "$results_dir/$base"
    else
      echo "PARSE ERROR: $wastfile — could not parse result line"
      echo "0 0" > "$results_dir/$base"
    fi
  else
    echo "NO RESULT: $wastfile"
    echo "0 0" > "$results_dir/$base"
  fi
}
export -f run_one

echo "Running ${#files[@]} .wast files with $jobs parallel jobs..."

printf '%s\n' "${files[@]}" | xargs -P "$jobs" -I {} bash -c 'run_one "$@"' _ {} "$exe" "$results_dir"

# Aggregate results
total_passed=0
total_tests=0
for f in "$results_dir"/*; do
  read -r p t < "$f"
  total_passed=$((total_passed + p))
  total_tests=$((total_tests + t))
done

echo "================"
if (( total_tests > 0 )); then
  percentage=$(awk "BEGIN { printf \"%.2f\", ($total_passed / $total_tests) * 100 }")
  echo "Total Passed: $total_passed/$total_tests ($percentage%)"
else
  echo "No tests run."
fi
