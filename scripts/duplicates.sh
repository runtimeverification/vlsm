#!/bin/sh
is_int() { test "$@" -eq "$@" 2> /dev/null; } 
DUPLICATES=$(find . -iname "*.v" -type f -printf "%f\n" | sort | uniq -cd) # a list of the duplicate filenames and their frequencies
echo "| Number of occurrences | Filename | Paths |"
echo "|:----------------------|:---------|:------|"
for i in $DUPLICATES
  do
    echo  -n " | $i " 
    find . -iname "$i" -exec echo -n "$1" {} \; | sed 's/\t/\t | /g; s/^/| /g; s/$/ |/g' # the paths to the files with the current name
    if ! is_int "$i" # if the value of variable i at the current iteration is not an integer, then it means it is a string (filename)
    then 
      echo
    fi
  done
