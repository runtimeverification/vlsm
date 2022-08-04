# Coq tool guide

This document describes how to use various tools to analyze the Coq code in the repository.

## coq-tools suite

[coq-tools](https://github.com/JasonGross/coq-tools) is a collection of Python 2 scripts that can manipulate Coq code.

### Installation

In order to use the scripts, Python 2 must be installed. For example, in a Debian-based Linux distribution such as Ubuntu:

```shell
sudo apt install python2
```

In Ubuntu, Python 2 can be made the default Python (although this is not strictly necessary for running coq-tools):

```shell
sudo update-alternatives --install /usr/bin/python python /usr/bin/python2 1
sudo update-alternatives --install /usr/bin/python python /usr/bin/python3 2
sudo update-alternatives --config python
```

Next, clone the coq-tools repository in a sibling directory of the Coq repository:

```shell
git clone https://github.com/JasonGross/coq-tools.git
```

### Minimizing requires

To minimize a single file's list of Coq require sentences, run the script `minimize-requires.py` from the Coq repository:

```shell
./../coq-tools/minimize-requires.py file.v --in-place .bak
```

In the single file case, all the projects `-Q` or `-R` options must be manually passed to the script.

To instead minimize the requires in the entire project without the need to manually pass paths, run the script from the directory where the `_CoqProject` file lives:

```shell
./../coq-tools/minimize-requires.py --all -f _CoqProject
```

Note that the results of running the script must be manually validated. If the script removes dependencies which are actually used, they will need to be added back manually.
