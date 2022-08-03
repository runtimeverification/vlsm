# `Minimizing-dependencies` script usage guide
## In order to use this set of Python scripts, make sure your Linux distributions provides Python2 and, in case it doesn't, install it and set it to default version.
```
   $ sudo apt install python2
   $ sudo update-alternatives --install /usr/bin/python python /usr/bin/python2 1
   $ sudo update-alternatives --install /usr/bin/python python /usr/bin/python3 2
   $ sudo update-alternatives --config python
```
## Clone the repository containing the set of Python scripts in a sibling directory 
`https://github.com/JasonGross/coq-tools.git`
## To minimize a single file's imports list, run the script like this (from inside the scripts directory),
`./../coq-tools/minimize-requires.py file.v  --in-place .bak`
## To minimize the imports in the entire project (from the directory where the `_CoqProject` file lives),
`coq-tools/minimize-requires.py --all -f _CoqProject`
### Note: Beware the fact that the script may delete also dependencies which are actually useful, hence you'll need to make an additional pass over the files/project and manually fix the imports.
