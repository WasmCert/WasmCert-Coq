#!/bin/bash
set -euo pipefail

folder="${1:-./wast_testsuite}"  
filter="${2:-}" 

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

total_passed=0
total_tests=0

for wastfile in "${files[@]}"; do
  echo "Running: $wastfile"
  tmpfile=$(mktemp)
  cleaned=$(mktemp)

  dune exec -- wasm_coq_interpreter --wast "$wastfile" | tee "$tmpfile"
  tr -d '\r' < "$tmpfile" | sed 's/\x1b\[[0-9;]*m//g' > "$cleaned"

  if result_line=$(grep -m1 "Result: " "$cleaned"); then
    if [[ "$result_line" =~ Result:\ ([0-9]+)/([0-9]+) ]]; then
      passed="${BASH_REMATCH[1]}"
      total="${BASH_REMATCH[2]}"
      total_passed=$((total_passed + passed))
      total_tests=$((total_tests + total))
    else
      echo "Regex match failed for $wastfile"
    fi
  else
    echo "No 'Result:' line found for $wastfile"
  fi
  rm -f "$tmpfile" "$cleaned"
done

echo "================"
if (( total_tests > 0 )); then
  percentage=$(awk "BEGIN { printf \"%.2f\", ($total_passed / $total_tests) * 100 }")
  echo "Total Passed: $total_passed/$total_tests ($percentage%)"
else
  echo "No tests run."
fi
