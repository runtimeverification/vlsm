#!/bin/sh
# Replace the comment-endings of type "**)", to "*)"
find . -iname "*.v" -exec sed -ie 's/\*\*)/\*)/' "{}" \;
find . -iname "*.v" -exec gawk -i inplace -f scripts/indentation1.awk "{}" \;
find . -iname "*.v" -exec gawk -i inplace -f scripts/comments.awk "{}" \;
find . -iname "*.v" -exec gawk -i inplace -f scripts/indentation.awk "{}" \;
find . -iname "*.ve" -exec rm "{}" \;
