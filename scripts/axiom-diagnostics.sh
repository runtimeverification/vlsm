#!/bin/sh

# If argument $1 is not present, print usage info and exit.
if test -z "$1"
then
  echo "Usage:"
  echo "make axioms"
  echo "make axioms path=path_to_source_directory"
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
`# Remove axiom types written inline.` \
-e '/ : .*/d' \
`# Remove axiom types written multiline.` \
-e '/^  .*/d' \
`# Simpler notice when no axioms were used.` \
-e 's/Closed under the global context/No Axioms/'

# Delete the temporary directory.
rm -rf "$tmp"
