!/bin/sh
find . -iname "*.v" -exec sed -i -e "s/[[:blank:]]*$//" "{}" \; 
