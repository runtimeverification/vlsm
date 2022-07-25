#!/bin/sh

# The list of duplicate filenames and their occurrence counts,
# sorted from most to least frequent.
duplicates=$(find . -iname "*.v" -type f -printf "%f\n" | sort -nr | uniq -cd)

# We will output the result as a markdown table. First comes the header.
echo "| Number of occurrences | Filename | Paths |"
echo "| --------------------- | -------- | ----- |"

# Iterate over the list.
# BEWARE: the list contains both numbers (occurence counts) and strings (filenames).
for i in $duplicates
do
  # Fill the first two columns of the current row.
  echo  -n "| $i "

  # Find paths of all files with the same name as $i
  # and print them (separated by spaces).
  find . -iname "$i" -exec echo -n "$1" {} \; \
  `# Now some hacky post-processing.` \
  | sed \
  `# Add a pipe at the beginning to mark the start of the last column.` \
  -e 's/^/|/' \
  `# Separate the paths with a <br> tag rather than spaces so that they are rendered on separate lines.` \
  -e 's/v \./v <br> ./g' \
  `# Add a space before that last pipe and add a newline character.` \
  -e 's/$/ |\n/g'
done
