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

### Install opam requirements (unless already installed)

A compiler and the unzip and bubblewrap tools are needed by opam.

To install on Debian-based distributions:

```shell
sudo apt-get update
sudo apt-get install -y build-essential unzip bubblewrap
```

To install on Fedora:

```shell
sudo dnf install @development-tools unzip bubblewrap
```

### Install opam (unless already installed)

We recommend installing opam via the official install script, which will always
install the latest released version:

```shell
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init
```

As an alternative, the opam package is included in the
standard repositories in some Linux distributions. In Fedora,
it can be installed by running:

```shell
sudo dnf install opam
```

### Initialize opam

Run `opam init`.

If you encounter the error "Sandboxing is not working on your platform", then
disable the sandboxing by choosing "Y".

Choose "y" in order to allow opam to modify `~/.profile`.

### <a name="switch-creation"></a>Install a switch for opam

```shell
opam switch create coq-8.17 --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda
```

### Update the current shell environment

```shell
eval $(opam env)
```

### <a name="dependencies-installation"></a>Install the project dependencies via opam

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.17.1 coq-stdpp.1.8.0 coq-itauto coq-equations
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

However, for the purposes of demonstration, we will assume the archive is called `2022.09.1.zip`.

```shell
wget https://github.com/coq/platform/archive/refs/tags/2022.09.1.zip
unzip 2022.09.1.zip
```

### Run the Platform scripts

```shell
cd platform-2022.09.1
./coq_platform_make.sh
```

### Activate the Platform switch

The Platform scripts will create a new opam switch, whose
name can be viewed by running `opam switch`. Here, we assume
the switch is called `__coq-platform.2022.09.1~8.16~2022.09`.

```shell
opam switch __coq-platform.2022.09.1~8.16~2022.09
eval $(opam env)
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

We recommend using the Visual Studio Code (VS Code) editor, which you can download and install from [here](https://code.visualstudio.com/).

After installing VS Code, you need to install the **Remote - WSL** extension. Click the *Connect to WSL* button, to open a new editor window in the WSL environment and open the project folder from inside this window.

Then, install the following extensions in the Remote WSL environment (assuming that [switch-creation](#switch-creation) and [dependencies-installation](#dependencies-installation) have been already done):

- [**Fast Unicode Math Characters** extension](https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode)
- [**VsCoq** Extension](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq):
```shell
code --install-extension coq-community.vscoq
```
OR
- [**Coq LSP** Extension](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq):
```shell
opam install coq-lsp && code --install-extension ejgallego.coq-lsp
```

After installing the above extensions, we recommend checking their instructions for basic usage.
