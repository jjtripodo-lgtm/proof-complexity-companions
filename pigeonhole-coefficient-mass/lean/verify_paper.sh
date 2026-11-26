#!/usr/bin/env bash
# Run at the pinned dependency revisions; does not fetch a build cache.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build PHP
audit="$(mktemp)"
trap 'rm -f -- "$audit"' EXIT
lake env lean -t 0 PaperAudit.lean | tee "$audit"
python3 - "$audit" <<'PY'
import pathlib
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
expected = set(re.findall(r"^#print axioms (\S+)$", pathlib.Path("PaperAudit.lean").read_text(), re.M))
actual = set()
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    m = re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", line)
    if not m:
        continue
    name, raw = m.groups()
    extra = set(raw.split(", ") if raw else []) - allowed
    if extra:
        raise SystemExit(f"{name}: unexpected axioms {sorted(extra)}")
    actual.add(name)
if expected != actual:
    raise SystemExit(f"Missing declarations: {sorted(expected - actual)}; unexpected: {sorted(actual - expected)}")
print(f"Verified {len(actual)} paper declarations; only standard axioms.")
PY
