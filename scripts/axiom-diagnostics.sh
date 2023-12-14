#!/bin/bash

# If argument $1 is not present, print usage info and exit.
if test -z "$1"
then
  echo "Usage:"
  echo "make axioms"
  echo "make axioms path=path_to_source_directory"
  echo "make axioms path=path_to_source_directory keep_tmp=true"
  echo "make axioms path=path_to_source_directory keep_tmp=true group_by_mod=true"
  exit
fi

# Nice name for argument $1.
COQLIBS=$1

# If argument $2 is not present, set it to current directory.
if test -z $2
then
  dir=.
else
  dir=$2
fi

# If argument $3 is set to true, then keep it. Otherwise set it to false.
if [[ $3 ]] && [ $3 == true ]
then
  keep_tmp=true
else
  keep_tmp=false
fi

# If argument $4 is present then store it
if test -n "$4"
then
   group_by_mod=$4
fi

# Create a temporary directory to hold intermediate results.
tmp=$(mktemp -d -p .)

# Find all Coq source files to be parsed.
for filepath in $(find $dir -name "*.v")
do
  # Import the module corresponding to the file that is being processed.
  echo $filepath \
  | \
  sed \
  -e 's/\.\.\///' \
  -e 's/\.\///' \
  -e 's/theories\//From VLSM Require Import /' \
  -e 's/\//./g' \
  -e 's/\.v/./' \
  >> "$tmp/tmp"

  # Replace definitions, lemmas etc. with Print Assumptions statements.
  # We also open a phony goal, so that we can use the idtac tactic
  # to print the name of the definition/lemma we are processing.
  lemma_name='\5'
  module_name=$(basename $filepath .v)
  full_name=$module_name.$lemma_name
  full_name_in_quotes='"'$full_name'"'
  cat $filepath \
  | \
  `# Filter out comments.` \
  awk 'BEGIN{ comment=0 } { if ($0 ~ /^ *\(\*.*\*\)$/) { next; } if ($0 ~ /^ *\(\*/) { comment = 1; next; } if ($0 ~ /\*\)$/) { comment = 0; next; } if (comment == 0) { print $0; } }' \
  | \
  sed -r \
  -e "s/\s*(Program)?\s*(Local|Global|#\[local\]|#\[global\])?\s*(Program)?\s*(Lemma|Theorem|Remark|Proposition|Corollary|Definition|Fixpoint|CoFixpoint|Inductive|Variant|CoInductive|Record|Class|Instance)\s+([_a-zA-Z0-9']+).*/Goal False. idtac $full_name_in_quotes. Abort. Print Assumptions $full_name./" \
  `# Filter out all attributes, including a trailing space.` \
  -e 's/\#\[[^]]*\] //' \
  `# Filter out all lines that are not about printing assumptions.` \
  -e '/^Goal.*Print Assumptions.*/!d' \
  `# Filter out some other problematic lines.` \
  -e '/andA/d' \
  -e '/\[/d' \
  `# And append the results to the temporary file.` \
  >> "$tmp/tmp"
done

# Add the .v extension to the temporary file so that coqc can process it.
mv "$tmp/tmp" "$tmp/tmp.v"

# Execute the temporary file - this prints assumption info about all definitions and lemmas to stdin.
coqc $COQLIBS "$tmp/tmp.v" \
`# We will do some post-processing.` \
| \
sed -r \
`# Remove axiom types written multiline.` \
-e '/^  .*/d' \
`# Remove axiom types written inline.` \
-e 's/([^:]*) : .*/\1/' \
`# Remove redundant lines and indent axioms listings.` \
| \
awk '{if (lastLine=="") {lastLine=$0;next} if ($0 ~ /Closed under the global context/) { print "\n"lastLine; lastLine=""; next; } if ($0 ~ /Axioms:/) { print "\n"lastLine; lastLine="" } else { print "\t"lastLine; lastLine=$0}}' \
`# Filter out axioms related to primitive integers.` \
| \
sed -r \
-e '/PrimInt63/d' \
-e '/Uint63/d' \
`# If the user passed group_by_mod=true then group the listings by module name.` \
| \
if [ "$group_by_mod" = "true" ]; then sed -E -e 's/\t/|/' -e '/^\|/!s/()\..*$//' | awk 'BEGIN {lastModule=""} {if ($0 ~ /^\|/) { data[lastModule][$0] = 1 } else { lastModule=$0 }} END {for (key in data) { print key; for (axiom in data[key]){ print "\t"axiom; } print "\n"; }}' | sed -E 's/\|//'; else tail -n +1; fi

# Delete the temporary directory (unless user wants to keep it).
if [ $keep_tmp == false ]
then
  rm -rf "$tmp"
fi
