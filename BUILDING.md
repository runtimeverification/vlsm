# VLSM Building Guide

This guide describes how to build (check) the code in the
[VLSM](https://github.com/runtimeverification/vlsm) project
using the [Coq proof assistant](https://coq.inria.fr).
The guide assumes a Unix shell, and some installation commands
assume a Debian-like Linux distribution, such as Ubuntu.

- [Building VLSM manually](#building-vlsm-manually)
- [Building VLSM using the Coq Platform](#building-vlsm-using-the-coq-platform)
- [Editor instructions](#editor-instructions)

Notes for Windows users:

- On Windows, we strongly recommend using WSL version 2 to install VLSM.
- Before beginning the VLSM installation process on Windows, you need to make sure that you have WSL installed on your machine and that this is set to version 2. A link providing instructions towards this is available on [Microsoft docs](https://docs.microsoft.com/en-us/windows/wsl/) and also [here](https://pureinfotech.com/install-windows-subsystem-linux-2-windows-10/) ([backup link](https://web.archive.org/web/20220712162626/https://pureinfotech.com/install-windows-subsystem-linux-2-windows-10/)).

## Building VLSM manually

### Ensure packages are up to date (optional)

```shell
sudo apt-get update
```

### Install opam (unless already installed)

```shell 
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)" 
opam init
```

Install the unzip and bubblewrap tools:

```shell
sudo apt-get install unzip 
sudo apt-get install -y bubblewrap
```
   
If you encounter the error "Sandboxing is not working on your platform ubuntu", then disable the sandboxing by choosing "Y".

Run again: `opam init`

Choose "y", in order to allow opam to modify `~/.profile`.

### Install a switch for opam

```shell
opam switch create coq-8.15 --packages=ocaml-variants.4.13.1+options,ocaml-option-flambda
```

### Update the current shell environment

```shell
eval $(opam env)
```

### Install the project dependencies via opam

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.15.2 coq-stdpp.1.7.0 coq-itauto
```

### Clone the project repository

```shell 
git clone https://github.com/runtimeverification/vlsm
```

### Build the project

```shell
cd vlsm
make -j $(nproc)
```

## Building VLSM using the Coq Platform

### Download and unpack the Coq Platform scripts

The latest Coq Platform release is always available using [this link](https://github.com/coq/platform/releases/latest). 

However, for the purposes of demonstration, we will assume the archive is called `2022.04.1.zip`.

```shell
wget https://github.com/coq/platform/archive/refs/tags/2022.04.1.zip
unzip 2022.04.1.zip
```

### Run the Platform scripts

```shell
cd platform-2022.04.1
./coq_platform_make.sh
```

### Activate the Platform switch

The Platform scripts will create a new opam switch, whose
name can be viewed by running `opam switch`. Here, we assume
the switch is called `__coq-platform.2022.04.1~8.15~2022.04`.

```shell
opam switch __coq-platform.2022.04.1~8.15~2022.04
eval $(opam env)
```

### Install the itauto library

```shell
opam install coq-itauto
```

### Clone the project repository

```shell 
git clone https://github.com/runtimeverification/vlsm
```

### Build the project

```shell
cd vlsm
make -j $(nproc)
```

## Editor instructions

We recommend using the Visual Studio Code editor, which you can download and install from [here](https://code.visualstudio.com/). 

After installing Visual Studio Code, you need to install the **Remote - WSL** extension. Click the *Connect to WSL* button, to open a new editor window in the WSL environment and open the project folder from inside this window.

Then install following extensions in the Remote WSL environment:

- [the **VsCoq** extension](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
- [the **Fast Unicode Math Characters** extension](https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode)

After installing the above extensions, we recommend checking their instructions for basic usage.
