# Waterproof

Waterproof is an educational tool in which students can interactively prove mathematical statements. Here is an example of an exercise and part of its solution in Waterproof.

Develop build status: [![Build Status](https://travis-ci.org/impermeable/waterproof.svg?branch=develop)](https://travis-ci.org/impermeable/waterproof)

![Screenshot of waterproof](WaterproofScreenshot.png)

## How to get started

The easiest way to get started with Waterproof is to:

* Install SerAPI following the steps below
* Install Waterproof using the installer from the [release page](http://github.com/impermeable/waterproof/releases)

### Installation of SerAPI

Waterproof communicates with the interactive theorem prover CoQ through the SerAPI library.

The following steps describe how to install SerAPI.

#### Step 1. Install opam

##### On Windows:
Install OCaml for Windows from https://fdopen.github.io/opam-repository-mingw/installation/. This also installs a cygwin terminal that you will need to use in the steps below.

##### On MacOS: 
Install opam by running the following commands in the terminal (taken from https://opam.ocaml.org/doc/Install.html#OSX)
```
brew install gpatch
brew install opam
```

##### On Linux:
Install opam, following instructions on https://opam.ocaml.org/doc/Install.html. For instance, for **Ubuntu**:
```
add-apt-repository ppa:avsm/ppa
apt update
apt install opam
```

#### Step 2. Install OCaml

OCaml for Windows installs a cygwin terminal. In the terminal, execute the following commands (corresponding to instructions on https://ocaml.org/docs/install.html). **Note:** On Windows, use the cygwin terminal that installed in the previous step.

First initialize the environment with
```
opam init
eval `opam env`
```

##### On Windows:
Install OCaml with
```
opam switch create 4.07.1+mingw64c
eval `opam env`
opam add repo ocaml_opam_repository https://github.com/ocaml/opam-repository.git
```

##### On Linux or macOS:
Install OCaml with
```
opam switch create 4.07.1
eval `opam env`
```

To see if you installed the correct version, execute
```
which ocaml
ocaml -version
```

#### Step 3. Install SerAPI with opam

After installing OCaml, run the following command in the terminal:

```
opam install coq-serapi
```

### Install Waterproof with the installer from the release page

After installing SerAPI, you are ready to install Waterproof using your preferred installer from the [release page](http://github.com/impermeable/waterproof/releases).

---

If you rather build the application yourself, you can follow [these steps](documentation/Cloning-the-repository.md).
