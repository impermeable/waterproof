# Waterproof

Waterproof is an educational tool in which students can interactively prove mathematical statements. Here is an example of an exercise and part of its solution in Waterproof.

Develop build status: [![Build Status](https://travis-ci.org/impermeable/waterproof.svg?branch=develop)](https://travis-ci.org/impermeable/waterproof)

![Screenshot of waterproof](WaterproofScreenshot.png)

## How to get started

The easiest way to get started with Waterproof is to follow the steps:

* Step 1. Install SerAPI following the steps below
* Step 2. Install Waterproof using the installer from the [release page](http://github.com/impermeable/waterproof/releases)

### Step 1. Installation of SerAPI

Waterproof communicates with the interactive theorem prover CoQ through the SerAPI library.

The following steps (1.a, 1.b and 1.c) describe how to install SerAPI.

#### Step 1.a Install opam

##### On Windows:
Install OCaml for Windows using the graphical installer on https://fdopen.github.io/opam-repository-mingw/installation/. This also installs a cygwin terminal that you will need to use in the steps below.

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

#### Step 1.b Install OCaml

In the terminal, execute the following commands (corresponding to instructions on https://ocaml.org/docs/install.html). **Note:** On Windows, use the cygwin terminal that installed in the previous step.

The first steps are common to all operating systems. First initialize the environment with
```
opam init
```
This may take a few minutes. In the meantime, opam will likely ask two questions. We recommend choosing 'y' to both, i.e. to opam modifying the `.bash_profile` and to opam adding a hook to the init scripts. Now execute the following line
```
eval `opam env`
```

##### On Windows:
Install OCaml with
```
opam switch create 4.11.1+mingw64c
eval `opam env`
```

In some cases, you may also need to add an extra repository:
```
opam repo add opam_ocaml_repository https://github.com/ocaml/opam-repository.git
```

##### On Linux or macOS:
Install OCaml with
```
opam switch create 4.11.1
eval `opam env`
```

#### Step 1.c Install SerAPI with opam

After installing OCaml, run the following command in the terminal:

```
opam install coq-serapi
```

Opam will ask to install several packages. Choose 'y' to install them. This step will at least take several minutes, but may take up to an hour.

Finally, execute again

```
eval `opam env`
```

### Step 2. Install Waterproof with the installer from the release page

After installing SerAPI, you are ready to install Waterproof using your preferred installer from the [release page](http://github.com/impermeable/waterproof/releases).

> **Known issue**: Because Waterproof is relatively unknown software, it is possible that it will initially be blocked by a virus scanner. To run Waterproof anyway: **on Windows:** Choose 'run anyway', **on Mac:** right-click and choose 'open software'; you may need to go to security settings to allow for running the app.

---

If you rather build the application yourself, you can follow [these steps](documentation/Cloning-the-repository.md).
