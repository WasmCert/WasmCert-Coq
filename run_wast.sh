#!/bin/bash
set -e

folder="${1:-./wast_testsuite}"  # Use argument, or fallback to default

total_passed=0
total_tests=0

for wastfile in "$folder"/*.wast; do
	if [[ "$wastfile" == *simd* ]]; then
		echo "Skipping SIMD test: $wastfile"
		continue
	fi
	echo "Running: $wastfile"
	tmpfile=$(mktemp)
	cleaned=$(mktemp)
	dune exec -- wasm_coq_interpreter --wast "$wastfile" | tee "$tmpfile"
	cat "$tmpfile" | tr -d '\r' | sed 's/\x1b\[[0-9;]*m//g' > "$cleaned"
	result_line=$(grep "Result: " "$cleaned")
	if [[ "$result_line" =~ Result:\ ([0-9]+)/([0-9]+) ]]; then
		passed="${BASH_REMATCH[1]}"
		total="${BASH_REMATCH[2]}"
		total_passed=$((total_passed + passed))
		total_tests=$((total_tests + total))
	else
		echo "Regex match failed for $$wastfile"
	fi
	rm -f "$tmpfile" "$cleaned"
done

echo "================"
percentage=$(awk "BEGIN { printf \"%.2f\", ($total_passed / $total_tests) * 100}")
echo "Total Passed: $total_passed/$total_tests ($percentage%)"