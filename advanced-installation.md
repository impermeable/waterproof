# Advanced installation on Windows (e.g. for developers)

1. Follow the steps under "Compiling from sources with Cygwin as build host" in the Windows install instructions on https://github.com/coq/platform
2. In particular, make sure you have activated the right opam switch as described in the build instructions
3. In the installed cygwin, execute ```opam install coq-serapi```
4. Clone the repository https://github.com/impermeable/coq-waterproof
5. With the installed cygwin, navigate to the folder in which coq-waterproof is located, execute ```make``` and then ```make install```.
