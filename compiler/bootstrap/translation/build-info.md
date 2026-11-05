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
holbuild -j4 build compiler64X64ProgTheory
```

The collector uses the HOL checkout selected by `holbuild context`. An
explicit HOL checkout can instead be supplied as its only argument.
`compilerProofTheory` and shared translation targets do not require this
preparation, because they do not depend on the provenance file.

The collector records the current UTC time, CakeML and selected HOL
revisions, and Poly/ML version. Tracked source modifications carry a dirty
fingerprint; unavailable revisions are reported as `unknown`. An unchanged
source/tool identity retains the producer's timestamp, so cached final
programs keep their original date. A different commit or dirty fingerprint
refreshes the metadata, invalidating final-program and bootstrap actions,
including their binary outputs.

`full_compile_32`, `full_compile_64` and `full_compile_host` now take the
build-information mlstring first. The shared main specifications quantify
over that string and its CakeML representation; their filesystem and
command-line premises are unchanged. `compiler32Prog`, `compiler64X64Prog`
and `compiler64Arm8Prog` bind the concrete string and retain unit entry
points. `compiler$compile` and `compile_correct` are unchanged.
