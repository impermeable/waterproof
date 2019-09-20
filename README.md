# Waterproof


## How to get working
To run the app [Node.js](https://nodejs.org/en/download/) needs to be installed.

To install the necessary node modules run:
```
npm install
```

To build the Electron app run:
```
npm run build-release
```

Finally, to start the application run:
```
npm start
```

## Waterproof notebooks and libraries

The repository now includes special Coq libraries. They focus on:

* *Tactics* that provide syntax closer to ordinary mathematics
* *Lemmas* that help in proving statements in Analysis

Currently, the library files (with extension `.vo`) are in the .gitignore, because they are likely to be platform-dependent. To use them, you will need to compile them yourself. 
They should be compiled, from the *wrapper* directory, to a library called wplib as follows:

```
sercomp -R "wplib","wplib" --mode=vo ".\wplib\Tactics\Tactics.v"
```

where `sercomp` should be replaced by the absolute sercomp path.

To import the libraries, it is important to add the correct directory to the loadpath. For instance, 
most of the notebooks are saved in the Notebooks folder. On Windows, if you double click on the filename in this folder, the working directory of WaterProof is automatically the Notebooks folder. To add the correct loadpath, you then need to add

```
Add LoadPath "..\..\".
```

at the beginning of the file. Next, the library can be imported with

```
Require Import wplib.Tactics.Tactics.
```

To see the current working directory of WaterProof, you can always use the command 

```
Pwd.
```

## Project structure
* `/app`:
This folder is for all static assets, i.e. files that don't need any pre-processing before being used by electron.

* `/e2e`:
This folder contains the project's end-to-end (integration) tests.

* `/src`:
This folder is for files that need to be transpiled or compiled before they can be used by Electorn.

* `/test`:
This folder contains the project's unit tests.

After being transpiled and/or compiled by the build process, the resulting files will be placed in the `/app` folder.
This way, the `/app` folder will contain the full application after building.
