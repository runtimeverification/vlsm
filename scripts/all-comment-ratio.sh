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
        case "$2" in
           tab)
              SEP="\t"
              ;;
           pipe)
              SEP="|"
              ;;
           csv)
              SEP=","
              ;;
           *)
              SEP="|"
              ;;
        esac
        shift 2
        ;;
    --) shift; 
        break 
        ;;
  esac
done

END=""
HEADERSEP="$SEP"
SEDSTRING=""

if [[ $SEP == "\t" || $SEP == "|" ]]; then
   END="|"
   SEDSTRING='s/\t/\t | /g; s/^/| /g; s/$/ |/g'
   HEADERSEP="|"
fi

BASE=$(dirname $0)
echo "$END Comments size $HEADERSEP Spec size $HEADERSEP Comments-Spec Ratio $HEADERSEP Spec-Comments Ratio $HEADERSEP Filename $END"
[[ $SEP == "\t" || $SEP == "|" ]] && echo "|:--------------|:----------|:--------------------|:--------------------|:---------|"
find . -iname "*.v" -exec $BASE/comment-ratio.sh $SEP "{}" \; | sort -n -k3 | sed "$SEDSTRING"


