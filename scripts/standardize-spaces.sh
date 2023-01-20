#!/bin/sh

# Add missing space after a comma.
sed -i 's/,\([^ ]\)/, \1/g' $(find -name "*.v")

# Add missing space after a semicolon.
sed -i 's/;\([^ ]\)/; \1/g' $(find -name "*.v")

# Add missing space after a tilde.
sed -i 's/~\([^ ]\)/~ \1/g' $(find -name "*.v")

# Add missing space around a :=
sed -i 's/:=\([^ ]\)/:= \1/g' $(find -name "*.v")
sed -i 's/\([^ ]\):=/\1 :=/g' $(find -name "*.v")

# Remove superfluous space after a '(' and before a ')'.
# Note: this might require manual tinkering to ensure no
# weird corner cases are present.
sed -i 's/( /(/g' $(find -name "*.v")
sed -i 's/ )/)/g' $(find -name "*.v")

# Remove superfluous space after a '[' and before a ']'.
# Note: this might require manual tinkering to ensure no
# weird corner cases are present.
sed -i 's/\[ /[/g' $(find -name "*.v")
sed -i 's/ ]/]/g' $(find -name "*.v")

# Add missing space around a |
sed -i 's/|\([^]}| -]\)/| \1/g' $(find -name "*.v")
sed -i 's/\([^[{| ]\)|/\1 |/g' $(find -name "*.v")

# Add missing space after a colon.
sed -i 's/:\([^ =:>/]\)/: \1/g' $(find -name "*.v")

# Add missing space before a colon and fix the known corner cases.
# Note: you should use `git add --patch` to browse through the changes
# manually and exclude the ones where the ':' was moved inside a comment.
sed -i 's/\([^ :]\):/\1 :/g' $(find -name "*.v")
sed -i 's/eqn :/eqn:/g' $(find -name "*.v")
sed -i 's/ eq :/ eq:/g' $(find -name "*.v")
sed -i 's/https :/https:/g' $(find -name "*.v")
sed -i 's/TODO :/TODO:/g' $(find -name "*.v")
sed -i 's/case :/case:/g' $(find -name "*.v")
sed -i 's/exact :/exact:/g' $(find -name "*.v")
sed -i 's/let :/let:/g' $(find -name "*.v")
sed -i 's/apply :/apply:/g' $(find -name "*.v")
sed -i 's/move :/move:/g' $(find -name "*.v")
sed -i 's/ \([0-9]\) :/ \1:/g' $(find -name "*.v")
sed -i 's/-\([0-9]\) :/-\1:/g' $(find -name "*.v")
