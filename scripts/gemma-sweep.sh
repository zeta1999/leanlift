#!/usr/bin/env bash
# gemma-sweep.sh — run the LLM-lane examples (the C++/Go/Solidity→Lean translation
# tests) across several LOCAL models and tabulate two things per cell:
#   (1) the verdict — L1 conformant / L0 typechecks-but-not / L0 FAILED / SKIPPED;
#   (2) the EFFECTIVE CONTEXT used — peak prompt tokens and max output tokens the
#       model actually ran, against the configured num_ctx, plus a TRUNCATED flag.
#
# Every config funnels through the instrumented `ollama` HTTP lane (run_ollama),
# so num_ctx is fixed (LEANLIFT_NUM_CTX, default 32768) and the token counts come
# straight from ollama's prompt_eval_count / eval_count. Responses are
# content-addressed per model in .leanlift-cache/, so re-runs are free.
#
# Needs: lean on PATH (elan), a release `lift`, and ollama serving the models.
set -uo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$HOME/.foundry/bin:$PATH"
export LEANLIFT_NUM_CTX="${LEANLIFT_NUM_CTX:-32768}"
# go-avg's oracle is `go build`; VCS stamping fails inside this git tree
# (exit 128). Disable it so the Go reference builds.
export GOFLAGS="${GOFLAGS:--buildvcs=false}"
LIFT=target/release/lift
OUT="${OUT:-/tmp/leanlift-sweep}"
mkdir -p "$OUT"

command -v lean >/dev/null 2>&1 || { echo "FATAL: lean not on PATH (elan)"; exit 1; }
[ -x "$LIFT" ] || { cargo build --release --quiet || { echo "build failed"; exit 1; }; }

# Each config: "label|lane|ENV=assignment". The gemma lane reads LEANLIFT_GEMMA_MODEL;
# the generic ollama lane reads LEANLIFT_OLLAMA_MODEL (used here for qwen, local).
# Comment a line out (or add gemma4:12b once ollama is new enough) as needed.
CONFIGS=(
  "gemma4:e4b|gemma|LEANLIFT_GEMMA_MODEL=gemma4:e4b"
  "gemma4:12b|gemma|LEANLIFT_GEMMA_MODEL=gemma4:12b"
  "gemma4:26b|gemma|LEANLIFT_GEMMA_MODEL=gemma4:26b"
  "qwen3.6:35b-a3b|ollama|LEANLIFT_OLLAMA_MODEL=qwen3.6:35b-a3b-bf16"
)

# The 11 examples whose front-end is Frontend::Llm (examples.rs). sol-dot2 needs
# `forge`; it will report SKIPPED/ERR without it.
TESTS=(cpp-streamed cpp-dot2 go-avg sol-dot2 cpp-isqrt cpp-bisect cpp-quant \
       cpp-fadd cpp-opt-gss cpp-opt-gd cpp-opt-hj)

# Skip a model that isn't actually pulled (e.g. 12b on an old ollama), with a note.
have_model() { ollama list 2>/dev/null | awk '{print $1}' | grep -qx "$1"; }

row() { printf "%-14s  %-26s  %-5s  %-6s  %-6s  %s\n" "$1" "$2" "$3" "$4" "$5" "$6"; }

for cfg in "${CONFIGS[@]}"; do
  IFS='|' read -r label lane assign <<<"$cfg"
  model="${assign#*=}"
  safe="$(echo "$label" | tr '/:' '__')"
  echo "================ $label   (lane=$lane, num_ctx=$LEANLIFT_NUM_CTX) ================"
  if ! have_model "$model"; then
    echo "  SKIP — model '$model' not pulled (ollama pull $model)"; echo; continue
  fi
  row "test" "verdict" "iters" "ptoks" "otoks" "trunc"
  for t in "${TESTS[@]}"; do
    log="$OUT/${safe}__${t}.log"
    env "$assign" "$LIFT" verify "$t" --lane "$lane" \
        --out "$OUT/${safe}__${t}.json" >"$log" 2>&1
    rc=$?
    verdict="$(grep -oE 'level: (L1 conformant/[0-9]+|L0 [A-Za-z]+|SKIPPED)' "$log" | head -1 | sed 's/level: //')"
    [ -z "$verdict" ] && verdict="ERR(rc=$rc)"
    iters="$(grep -oE 'settled after [0-9]+ iter' "$log" | grep -oE '[0-9]+' | head -1)"
    ptoks="$(grep -oE 'prompt_tokens=[0-9]+' "$log" | grep -oE '[0-9]+' | sort -n | tail -1)"
    otoks="$(grep -oE 'output_tokens=[0-9]+' "$log" | grep -oE '[0-9]+' | sort -n | tail -1)"
    grep -qE 'ctx TRUNCATED' "$log" && trunc="YES" || trunc="no"
    row "$t" "$verdict" "${iters:-–}" "${ptoks:-–}" "${otoks:-–}" "$trunc"
  done
  echo
done

echo "logs + per-cell report.json under: $OUT"
echo "ptoks = peak prompt tokens (effective input context), otoks = max output tokens, vs num_ctx=$LEANLIFT_NUM_CTX"
