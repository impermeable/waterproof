# Advanced installation on Windows (e.g. for developers)

1. Follow the steps under "Compiling from sources with Cygwin as build host" in the Windows install instructions on https://github.com/coq/platform
2. Convert the files to unix line endings with ```find . -type f -print0 | xargs -0 dos2unix``` from cygwin
3. In particular, make sure you have activated the right opam switch as described in the build instructions
4. In the installed cygwin, execute ```opam install coq-serapi```
5. Clone the repository https://github.com/impermeable/coq-waterproof
6. With the installed cygwin, navigate to the folder in which coq-waterproof is located, execute ```make``` and then ```make install```.
