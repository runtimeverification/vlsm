#!/bin/sh
#| Paper           | Coq                              |
#|:----------------|:---------------------------------|
BASE=$(dirname $0)
echo "| Comments size | Spec size | Comments-Spec Ratio | Spec-Comments Ratio | Filename |"
echo "|:--------------|:----------|:--------------------|:--------------------|:---------|"
find . -iname "*.v" -exec $BASE/comment-ratio.sh "{}" \; | sort -n -k3 | sed 's/\t/\t | /g; s/^/| /g; s/$/ |/g'