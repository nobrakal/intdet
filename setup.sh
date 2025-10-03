#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

export OPAMYES=true

# Update the package list.
echo "Updating the list of available packages..."
opam update

# Create a local switch. (We assume opam 2 is installed.)
echo "Creating a local switch..."

opam switch --switch . import packages.switch
eval "$(opam env --set-switch)"

eval $(opam env)

echo "Compiling..."
make
