#!/bin/sh
BASE=$(dirname $0)
echo "| Number of occurrences | Filename | Paths |"
echo "|:----------------------|:---------|:------|"
is_int() { test "$@" -eq "$@" 2> /dev/null; } 
DUPLICATES=$(find . -iname "*.v" -type f -printf "%f\n" | sort | uniq -cd)
for i in $DUPLICATES
    do
        echo  -n " $i "
        find . -iname "$i" -exec $BASE/filenames.sh "{}" \; | sed 's/\t/\t | /g; s/^/| /g; s/$/ |/g'
        if ! is_int "$i"
        then 
            echo
        fi
    done
