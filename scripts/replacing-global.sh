#!/bin/sh
BASE=$(dirname $0)
find . -iname "*.v" -exec sed -i -e 's/#\[global\]\(.*\)Instance/#\[export\]\1Instance/' "{}" \;