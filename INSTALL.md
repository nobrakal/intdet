# Setup & Build Instructions

This project needs [opam](https://opam.ocaml.org/doc/Install.html) to
install dependencies.
This project uses the [dune](https://dune.build/) build system.

You can run `./setup.sh` to create a local opam switch with correct
dependencies, and build the project.
Please allow at least 30 minutes for the installation and build to
run.

If you run into troubles, the file `packages.switch` contains
the exact list of ocaml packages that need to be installed.

To manually build the project, run `make` or `dune build`.
