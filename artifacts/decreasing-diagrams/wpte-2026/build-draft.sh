#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

mkdir -p build
TEXINPUTS=./eptcs-style//: latexmk -g -pdf -interaction=nonstopmode -halt-on-error -cd -outdir=build wpte2026-draft.tex
