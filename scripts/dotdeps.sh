#!/bin/sh
(echo "digraph interval_deps {" ;
echo "node [shape=ellipse, style=filled, URL=\"VLSM.\N.html\", color=black];";
coqdep -Q theories/VLSM VLSM $* | sed -e 's,theories/,,g' | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
while read src dst; do
    color=$(echo "$src" | sed -e 's,VLSM.Lib.*,turquoise,;s,VLSM.Core.*,plum,;s,[A-Z].*,white,')
    echo "\"$src\" [fillcolor=$color];"
    for d in $dst; do
	echo "\"$src\" -> \"${d%.vo}\" ;"
    done
done;
echo "}") | tred
