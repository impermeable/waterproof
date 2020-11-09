# Instructions on cloning the Waterproof repository

Here we describe how you can clone the Waterproof repository, and build the application yourself.

## Clone this repository

First clone the repository. For this, you would need [git](https://git-scm.com/downloads). Then, in a terminal (from a directory in which you want to install the folder with all Waterproof files) execute
```
git clone https://github.com/impermeable/waterproof.git
```
The move into the waterproof directory
```
cd waterproof
```

## Install Node.js

Install Node.js, for instance from [Node.js](https://nodejs.org/en/download/)

## Install the necessary modules

In a terminal, move to the Waterproof base directory. Then, to install the necessary Node.js modules, run:
```
npm install
```

It may be necessary to update the modules with
```
npm update
```

## Run the app in developer mode
To run Waterproof in developer mode run
```
npm run electron:serve
```

## Build the electron app

To build the Electron app run:
```
npm run electron:build
```
An installer will be produced in the folder `dist_electron`.
