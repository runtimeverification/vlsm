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

The minimization script included in the Coq repository will operate on absolutized imports.
For example, `Require Import Coq.Lists.List` is the absolutized version of `From Coq Require Import List`.
When in the project's root directory, run the following to absolutize the imports of a file `file.v`:

```shell
./../coq-tools/absolutize-imports.py path/to/file.v --in-place .bak
```

In this single file case, all the project's `-Q`/`-R` options must be manually passed to the script. To instead absolutize the import sentences in the entire project without the need to manually pass any paths, run the script from the directory where the `_CoqProject` file lives:

```shell
./../coq-tools/absolutize-imports.py -f _CoqProject --update-all 
```


To minimize the list of require sentences for a file `file.v` run the script `minimize-requires.py` from the Coq repository:

```shell
./../coq-tools/minimize-requires.py path/to/file.v --in-place .bak
```

To minimize the require sentences for the whole project:

```shell
./../coq-tools/minimize-requires.py --all -f _CoqProject
```

Note that the results of running the script must be manually validated. If the script removes dependencies which are actually used, they will need to be added back manually.

## Axiom use analysis

To do basic axiom use analysis for the project as a whole, run the
following command in the project root directory:

```shell
make validate
```

To do detailed axiom use analysis for all files in a certain directory,
for example `theories/CBC`, run the following command in the project
root directory:

```shell
make axioms path=theories/CBC
```

## Stripping newlines 

To strip consecutive newlines exceeding a certain number, run the `strip-newlines.py` script, passing as command line argument `max + 1` (where max is the maximum number of consecutive newlines you want to accept). 

In case you pass a negative number as argument, the content will remain unchanged, and if the argument you pass is `0`, then all strings of consecutive newlines will be replaced by a single space.

For example, if you want to limit the number of consecutive newlines to 1, run:

## Analyzing commments and specifications

To analyze comment and specification usage throughout the project (for all `*.v` files), run:

```shell
./all-comment-ratio.v
```

This will output a table whose columns correspond (in this order) to: comment size, specification size, ratio between comments and specifications, ratio between specifications and comments, filename.

```shell
python scripts/strip-newlines.py 2
```
