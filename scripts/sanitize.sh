#!/bin/sh
BASE=$(dirname $0)
find . -iname "*.v" -exec sed -i -f "$BASE/sanitize.sed" "{}" \;