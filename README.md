# Waterproof

Waterproof is an educational tool in which students can interactively prove mathematical statements. Here is an example of an exercise and part of its solution in Waterproof.

Develop build status: [![Build Status](https://travis-ci.org/impermeable/waterproof.svg?branch=develop)](https://travis-ci.org/impermeable/waterproof)

![Screenshot of waterproof](WaterproofScreenshot.png)

## How to get started

The easiest way to get started with Waterproof is to follow the steps:

* Step 1. Install SerAPI following the steps below
* Step 2. Install Waterproof using the installer from the [release page](http://github.com/impermeable/waterproof/releases)

**Note**: If you cannot get the installation to work, see the bottom of this page for an alternative fool-proof installation, where we give a virtual disk image with waterproof and its dependencies preinstalled. However, we do not recommend doing this firstly, as it is slow solution and requires a lot more disk space.

### Step 1 for Windows. Installation of SerAPI.

* Download the _graphical installer_ for Ocaml for Windows from https://fdopen.github.io/opam-repository-mingw/installation/.
* Windows could indicate that the software is not used by many people. To use the software anyway, choose _keep_.
* Select the .exe file, then right click on the .exe file, and choose *Run as administrator*. This also installs a cygwin terminal that you will need to use in the steps below.
* Windows could still block the installer from running. To run the installer anyway, choose _More info_, and then _Run anyway_.
* Run as administrator the cygwin terminal you just installed. In the terminal, type ```opam install coq-serapi``` and press enter. Choose 'Y'. This step could take up to an hour.

If this worked, you can continue with Step 2.

### Step 1 for MacOS and Linux. Installation of SerAPI.

The following steps (1.a, 1.b and 1.c) describe how to install SerAPI on MacOS or Linux.

#### Step 1.a for MacOS and Linux: Install opam

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

#### Step 1.b for MacOS and Linux: Install an OCaml compiler

In the terminal, execute the following commands (corresponding to instructions on https://ocaml.org/docs/install.html). **Note:** On Windows, run the cygwin terminal that was installed as administrator, and execute the next commands in the terminal.

The first steps are common to all operating systems. First initialize the environment with
```
opam init
```
This may take a few minutes. In the meantime, opam will likely ask two questions. We recommend choosing 'y' to both, i.e. to opam modifying the `.bash_profile` and to opam adding a hook to the init scripts. Now execute the following line
```
eval `opam env`
```

##### On Linux or macOS:
Install OCaml with
```
opam switch create 4.11.1
eval `opam env`
```

#### Step 1.c for MacOS and Linux: Install SerAPI with opam

After installing OCaml, run the following command in the terminal:

```
opam install coq-serapi
```

Opam will ask to install several packages. Choose 'y' to install them. This step will at least take several minutes, but may take up to an hour.

Finally, execute again

```
eval `opam env`
```

#### Step 1 common errors
When installing opam packages in linux, a common error is caused by missing system packages. You will have to check the error message to find out which package this is. For instance, it could be you are missing one of these packages: m4, build, dune-configurator. In which case, these can be installed using, for instance:

```
sudo apt-get install m4
``` 

### Step 2. Install Waterproof with the installer from the release page

After installing SerAPI, you are ready to install Waterproof using your preferred installer from the [release page](http://github.com/impermeable/waterproof/releases).

> **Known issue**: Because Waterproof is relatively unknown software, it is possible that it will initially be blocked by a virus scanner. To run Waterproof anyway: **on Windows:** Choose 'run anyway', **on Mac:** right-click and choose 'open software'; you may need to go to security settings to allow for running the app.

---

If you rather build the application yourself, you can follow [these steps](documentation/Cloning-the-repository.md).

#### Step 2 common errors
Upon launch of Waterproof, a common fault yields a file viewer titled 'Please select the program named sertop'. Waterproof depends on `sertop` (which was installed with `coq-serapi` in Step 1), so we need to find it. It is installed in a switch (a folder called `4.11.1` perhaps) in opam. Opam packages are installed in a `.opam\[switch]\bin` folder, usually found under your user's base folder.

Note that `.opam` is a hidden folder, so you will need to show hidden files, which is done differently per operating system. To show hidden folders:
* on Windows: Open File Explorer, Select View > Options > Change folder and search options. Select the View tab and, in Advanced settings, select Show hidden files, folders, and drives and OK.
* on Linux: From a GUI file manager, go to View and check the option Show Hidden Files
* on Mac: Press Cmd + Space to open a Terminal. In here, type:
```
defaults write com.apple.Finder AppleShowAllFiles true
killall Finder
```
> **Note for Mac users**: The latter setting can be undone by replacing `true` with `false`, should you want to hide your hidden folders again, but this is totally unnecessary. On Mac we recommend searching for Sertop in a separate file viewer (Finder) window instead of the pop-up, as hidden folders are not always shown here despite enabling the setting.

Common places to look for `.opam` and then `.opam\[switch]\bin\sertop` are:
* on Windows `C:\OCaml64\home\[your user]`
* on Linux/MacOs: `\home\[your user]`

Finally, if you still cannot find sertop, but you can find `.opam\[switch]\bin`, then there was likely an error in Step 1 and the installation of coq-serapi was not completed.

### Alternative installation

The alternative installation works only on 64-bit OS's, but not really recommend as it requires a few gigabytes of disk space. 

* Download and install [Virtual Box](https://www.virtualbox.org/) or similar VM software.
* [Download the VM image](https://drive.google.com/file/d/1xo7wNrn7UfhYTh6eakgSqSB84nmHsntc/view?usp=sharing)
* Open Virtual Box. Then, press File > Import Appliance > Choose file. Navigate to the extracted VM image called `Preinstalled_Waterproof.ova`. Choose this file, and press next. The settings should be fine, so just press Import. This may take a while...
* You should be welcomed by a log in screen. The username and password is: `waterproof`. On the desktop, you can find a shortcut to Waterproof which you can double-click to execute.
* You may want to change the monitor settings. For this, go to the bottom left menu button > Preferences > Monitor settings

> **Note** In order to transfer files between the virtual machine and your own filesystem, you could use Google Drive or something similar. An more sleak alternative is creating a shared disk partition, but it defeats the purpose of a simple installation.