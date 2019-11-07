# Intructions on cloning the Waterproof repository

## Clone this repository

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
npm run build-release
```
An installer will be produced in the folder `dist_electron`.

Finally, to start the application run:
```
npm start
```
