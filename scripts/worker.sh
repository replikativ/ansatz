#!/usr/bin/env bash
# Start a Codex worker on a quality task (docs/QUALITY_PLAN.md, docs/quality/WORKER_GUIDE.md).
#
#   scripts/worker.sh ID [BASE]       create worktree ../ansatz-wt/ID on branch quality/ID from BASE
#                                     (default: current branch) and run codex exec there in the
#                                     background; the brief is docs/quality/tasks/ID.md (committed
#                                     on BASE)
#   scripts/worker.sh review ID       run a Codex review of branch quality/ID against BASE
#
# Logs and the worker's final message go to /tmp/claude-1000/ansatz-workers/ID.{log,last.md}.
# MODEL / EFFORT override the model (default gpt-6.1-sol) and reasoning effort (default medium).
set -euo pipefail

REPO=$(git rev-parse --show-toplevel)
WT_ROOT=$(dirname "$REPO")/ansatz-wt
OUT=/tmp/claude-1000/ansatz-workers
MODEL=${MODEL:-gpt-6.1-sol}
EFFORT=${EFFORT:-medium}
mkdir -p "$WT_ROOT" "$OUT"

codex_run() {  # dir prompt id
  local dir=$1 prompt=$2 id=$3
  nohup codex exec -m "$MODEL" -c model_reasoning_effort="\"$EFFORT\"" \
    -c sandbox_workspace_write.network_access=true \
    -s workspace-write --add-dir /tmp/claude-1000 \
    -C "$dir" -o "$OUT/$id.last.md" "$prompt" > "$OUT/$id.log" 2>&1 &
  echo $! > "$OUT/$id.pid"
  echo "worker $id: pid $(cat "$OUT/$id.pid"), log $OUT/$id.log"
}

if [ "${1:-}" = "review" ]; then
  id=${2:?id}; base=${3:-$(git -C "$REPO" rev-parse --abbrev-ref HEAD)}
  wt=$WT_ROOT/$id
  prompt="You are reviewing branch quality/$id (the diff against $base: git diff $base...HEAD) in this
worktree. Read docs/quality/WORKER_GUIDE.md, the brief docs/quality/tasks/$id.md and the worker's
result docs/quality/results/$id.md. Review the diff for correctness against the Lean 4 source in
/home/christian-weilbach/Development/lean4 (check the cited Lean functions yourself, not the
worker's summary), for kernel soundness, for violations of the guide (broad catches, silent caps,
scope fence), and for tests that do not test what they claim. Do not edit code. You may start a
REPL per the guide (port: the brief's port + 100) to reproduce a suspected bug. Write
docs/quality/reviews/$id.md: findings ranked by severity, each with file:line, the concrete failing
scenario, and confidence; then a verdict MERGE / FIX-FIRST / REJECT. Commit it."
  codex_run "$wt" "$prompt" "$id-review"
  exit 0
fi

id=${1:?id}; base=${2:-$(git -C "$REPO" rev-parse --abbrev-ref HEAD)}
wt=$WT_ROOT/$id
git -C "$REPO" show "$base:docs/quality/tasks/$id.md" > /dev/null \
  || { echo "brief docs/quality/tasks/$id.md is not committed on $base" >&2; exit 1; }
if [ ! -d "$wt" ]; then
  git -C "$REPO" worktree add -q -b "quality/$id" "$wt" "$base"
  # compiled Java kernel classes are gitignored; the worktree needs them on its classpath
  cp -r "$REPO/classes" "$wt/classes"
fi
prompt="Read docs/quality/WORKER_GUIDE.md, then your task brief docs/quality/tasks/$id.md, in this
worktree (branch quality/$id). Do the task as the brief and the guide say, commit on your branch,
and finish with the result file docs/quality/results/$id.md."
codex_run "$wt" "$prompt" "$id"
