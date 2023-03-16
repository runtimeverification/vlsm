#!/bin/sh
#| Paper           | Coq                              |
#|:----------------|:---------------------------------|

# Usage: all-comment-ratio.sh [--separator tab|pipe] | [-s tab|pipe]


VALID_ARGS=$(getopt -o s: --long separator: -- "$@")
if [[ $? -ne 0 ]]; then
    exit 1;
fi

SEP="\t"

eval set -- "$VALID_ARGS"
while [ : ]; do
  case "$1" in
    -s | --separator)
        echo "Processing 'gamma' option. Input argument is '$2'"
        echo $2
        if [[ "$2" == "tab" ]]; then SEP="\t"; else SEP="|"; fi
        shift 2
        ;;
    --) shift; 
        break 
        ;;
  esac
done

BASE=$(dirname $0)
echo "| Comments size | Spec size | Comments-Spec Ratio | Spec-Comments Ratio | Filename |"
echo "|:--------------|:----------|:--------------------|:--------------------|:---------|"
find . -iname "*.v" -exec $BASE/comment-ratio.sh $SEP "{}" \; | sort -n -k3 | sed 's/\t/\t | /g; s/^/| /g; s/$/ |/g'


