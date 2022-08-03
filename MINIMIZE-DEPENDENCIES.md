# `Minimizing-dependencies` script usage guide

In order to use this set of Python scripts, make sure your Linux distribution provides Python 2 and. In case it doesn't, install it and set it to default version.

```
sudo apt install python2
sudo update-alternatives --install /usr/bin/python python /usr/bin/python2 1
sudo update-alternatives --install /usr/bin/python python /usr/bin/python3 2
sudo update-alternatives --config python
```
Clone the repository containing the set of Python scripts in a sibling directory.

```shell
git clone https://github.com/JasonGross/coq-tools.git
```

To minimize a single file's imports list, run the script from inside the scripts directory:

```shell
./../coq-tools/minimize-requires.py file.v  --in-place .bak
```

To minimize the imports in the entire project, run the script from the directory where the `_CoqProject` file lives:

```shell
coq-tools/minimize-requires.py --all -f _CoqProject
```

**Beware!** The script may also delete dependencies which are actually used, hence you'll need to make an additional pass over the files/project and manually fix the imports.
