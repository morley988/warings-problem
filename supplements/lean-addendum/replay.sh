#!/bin/sh
set -eu
base_dir=$1
addendum_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$base_dir"
python3 verification-scripts/replay.py
cp -R "$addendum_dir/source/." .
mkdir -p .lake/build/lib/lean/WaringFieldSmall
lake env lean -j1 -o .lake/build/lib/lean/WaringFieldSmall/All.olean WaringFieldSmall/All.lean
