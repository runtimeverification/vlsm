#!/bin/sh



# Extract command line arguments 
VALID_ARGS=$(getopt -o hs: --long help,separator: -- "$@")
if [[ $? -ne 0 ]]; then
    exit 1;
fi

# Set default separator to tab
SEP="\t"

# Pattern match the separator selection
eval set -- "$VALID_ARGS"
while [ : ]; do
  case "$1" in
    -h | --help) 
        echo "Usage: all-comment-ratio.sh [--separator csv|tab|pipe] | [-s csv|tab|pipe]"
        exit
        ;;
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

# Additional formatting
if [[ $SEP == "\t" || $SEP == "|" ]]; then
   END="|"
   SEDSTRING='s/\t/\t | /g; s/^/| /g; s/$/ |/g'
   HEADERSEP="|"
fi

BASE=$(dirname $0)

# Print header information
echo "$END Comments size $HEADERSEP Spec size $HEADERSEP Comments-Spec Ratio $HEADERSEP Spec-Comments Ratio $HEADERSEP Filename $END"
[[ $SEP == "\t" || $SEP == "|" ]] && echo "|:--------------|:----------|:--------------------|:--------------------|:---------|"

# Run the ratio script on all *.v files
find . -iname "*.v" -exec $BASE/comment-ratio.sh $SEP "{}" \; | sort -n -k3 | sed "$SEDSTRING"


