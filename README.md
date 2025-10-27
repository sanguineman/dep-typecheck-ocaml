# Dependent types type-checker

A simple dependent type checker implemented in OCaml for the KAIST CS520(*Principles of Programming Languages*) course project.
The implementation is based on the algorithm described in *"An Algorithm for Type-Checking Dependent Types"* by **Thierry Coquand**.

## Build
### Set up an opam local switch
```bash
opam switch create . ocaml-base-compiler.5.2.1
eval $(opam env)
```

### Install dependencies
```bash
opam install dune ocaml-lsp-server odoc
```

### Build the project
```bash
dune build
```

### Running the type-checker
```bash
dune exec bin/main.exe
```

