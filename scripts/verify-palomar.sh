#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <path-to-Lean-project>" >&2
  exit 2
fi

repository_root=$(cd "$(dirname "$0")/.." && pwd)
project_dir=$(cd "$repository_root/$1" && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3 ruby; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required" >&2
    exit 1
  fi
done

for required_file in lakefile.toml lean-toolchain lake-manifest.json Challenge.lean Solution.lean comparator.json formalization.yaml; do
  if [ ! -f "$project_dir/$required_file" ]; then
    echo "error: missing $project_dir/$required_file" >&2
    exit 1
  fi
done

for required_file in LICENSE scripts/landrun-wrapper.sh scripts/validate-formalization.rb; do
  if [ ! -f "$repository_root/$required_file" ]; then
    echo "error: missing $repository_root/$required_file" >&2
    exit 1
  fi
done

ruby "$repository_root/scripts/validate-formalization.rb" "$project_dir/formalization.yaml"

python3 - "$project_dir/comparator.json" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if config.get("enable_nanoda") is not True:
    raise SystemExit("enable_nanoda must be exactly true")
if not config.get("theorem_names"):
    raise SystemExit("theorem_names must be nonempty")
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

project_toolchain=$(tr -d '[:space:]' < "$project_dir/lean-toolchain")
export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match Lean4export $export_toolchain" >&2
  exit 1
fi

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$project_dir"
lake exe cache get
chmod +x "$repository_root/scripts/landrun-wrapper.sh"
PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
