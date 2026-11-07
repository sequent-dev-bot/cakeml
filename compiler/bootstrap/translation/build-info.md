# Compiler build information

The compiler prints its build information for `--version`. Its timestamp,
CakeML and HOL revisions, and Poly/ML version belong to the final program,
so changing them does not invalidate the compiler correctness proof or
shared compiler translations.

`compilerBuildInfoTheory` reads `compiler_build_info.txt`, a declared build
input. Native Holmake collects it automatically. Before each holbuild
invocation that builds a final compiler program or bootstrap target, collect
it explicitly from the repository root:

```sh
holbuild buildhol
sh compiler/bootstrap/translation/update_compiler_build_info.sh
holbuild -j4 build compiler_x64ProgTheory
```

The collector uses the HOL checkout selected by `holbuild context`. An
explicit HOL checkout can instead be supplied as the first argument; an
optional second argument selects Poly/ML. `HOLBUILD_POLY` overrides that
selection. Native Holmake supplies its configured Poly/ML executable.
To override the collector's Poly/ML selection for a native build, set
`HOLBUILD_POLY` in the environment to the executable used by that build.
A command-line `Holmake POLY=...` override alone can refresh the
metadata twice while Holmake parses its dependencies, changing the
timestamp even when the source identity is unchanged.
`compilerProofTheory` and shared translation targets do not require this
preparation, because they do not depend on the provenance file.

The collector records the current UTC time, CakeML and selected HOL
revisions, and Poly/ML version. Tracked source modifications carry a dirty
fingerprint; unavailable revisions are reported as `unknown`. An unchanged
source/tool identity retains the producer's timestamp, so cached final
programs keep their original date. A different commit or dirty fingerprint
refreshes the metadata, invalidating final-program and bootstrap actions,
including their binary outputs.
The three bootstrap theories declare their generated `cake.S` files as
outputs; x64 and ARM8 also declare `config_enc_str.txt`. Holbuild preserves
these files after execution and restores them with cached theories.
The S-expression export similarly declares its generated `cake-sexpr` file.

`full_compile` and `full_compile_host` take the build-information mlstring
first. The shared main specifications quantify
over that string and its CakeML representation; their filesystem and
command-line premises are unchanged. `compiler_ag32Prog`, `compiler_x64Prog`
and `compiler_arm8Prog` bind the concrete string and retain unit entry
points. `compiler$compile` and `compile_correct` are unchanged.
