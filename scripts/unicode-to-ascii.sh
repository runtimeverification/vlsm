#!/bin/sh

# Find all files that contain Unicode characters that we don't like.
files=$(grep -El "∧|∨|→|↔|∀|∃|≠" $(find -name "*.v"))

# Replace each unicode character with its ASCII equivalent.
sed -i 's/∧/\/\\/g' $files
sed -i 's/∨/\\\//g' $files
sed -i 's/→/->/g' $files
sed -i 's/↔/<->/g' $files
sed -i 's/∀/forall/g' $files
sed -i 's/∃/exists/g' $files
sed -i 's/≠/<>/g' $files
