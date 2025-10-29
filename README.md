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
opam install dune ocaml-lsp-server odoc ocamlformat bisect-ppx
```

### Build the project
```bash
make
```

### Running the type-checker
```bash
dune exec bin/main.exe
```

## Testing
To run the test suite, use the following command:
```bash
make test
```
This will execute the test cases located in the `test/` directory and display the results.

## Coverage
To generate a code coverage report, run:
```bash
make coverage
```
This will create an HTML report in the `_coverage` directory, which you can open in your web browser to view the coverage details.
