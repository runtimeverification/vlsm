#!/bin/sh

# If argument $1 is not present, print usage info and exit.
if test -z "$1"
then
  echo "Usage:"
  echo "make axioms"
  echo "make axioms path=path_to_source_directory"
  echo "make axioms path=path_to_source_directory keep_tmp=true"
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

# Create a temporary directory to hold intermediate results.
tmp=$(mktemp -d)

# Find all Coq source files to be parsed.
for filepath in $(find $dir -name "*.v")
do
  # Import the module corresponding to the file that is being processed.
  echo $filepath \
  | \
  sed \
  -e 's/\.\.\///' \
  -e 's/\.\///' \
  -e 's/theories\//Require Import /' \
  -e 's/\//./g' \
  -e 's/\.v/./' \
  >> "$tmp/tmp"

  # Replace definitions, lemmas etc. with Print Assumptions statements.
  # We also open a phony goal, so that we can use the idtac tactic
  # to print the name of the definition/lemma we are processing.
  lemma_name='"\5"'
  module_name=$(basename $filepath .v)
  sed -r \
  -e "s/\s*(Program)?\s*(Local|Global|#\[local\]|#\[global\])?\s*(Program)?\s*(Lemma|Theorem|Remark|Proposition|Corollary|Definition|Fixpoint|CoFixpoint|Inductive|Variant|CoInductive|Record|Class|Instance)\s+([_a-zA-Z0-9']+).*/Goal False. idtac $lemma_name. Abort. Print Assumptions $module_name.\5./" \
  `# Filter out all attributes, including a trailing space.` \
  -e 's/\#\[[^]]*\] //' \
  `# Filter out all lines that are not about printing assumptions.` \
  -e '/^Goal.*Print Assumptions.*/!d' \
  `# Filter out some other problematic lines.` \
  -e '/andA/d' \
  -e '/\[/d' \
  $filepath \
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
awk '{if (lastLine=="") {lastLine=$0;next} if ($0 ~ /Closed under the global context/) {lastLine=""; next; } if ($0 ~ /Axioms:/) { print "\n"lastLine; lastLine="" } else { print "\t"lastLine; lastLine=$0}}' \
`# Filter out axioms related to primitive integers.` \
| \
sed -r \
-e '/PrimInt63/d' \
-e '/Uint63/d'

# Delete the temporary directory (unless user wants to keep it).
if [ $keep_tmp == false ]
then
  rm -rf "$tmp"
fi
