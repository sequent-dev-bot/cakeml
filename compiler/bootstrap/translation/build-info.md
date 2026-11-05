# Compiler build information

The compiler prints its build information for `--version`. Its timestamp,
CakeML and HOL revisions, and Poly/ML version belong to the final program,
so changing them does not invalidate the compiler correctness proof or
shared compiler translations.

`compilerBuildInfoTheory` reads `compiler_build_info.txt`. Native Holmake
refreshes this input when building a final compiler program. Before building
one with holbuild, collect the information using the HOL checkout returned
by `holbuild buildhol`:

```sh
sh compiler/bootstrap/translation/update_compiler_build_info.sh /path/to/HOL
holbuild -j4 build compiler64X64ProgTheory
```

The HOL checkout must be the one used for the build. The collector records
the current UTC time, marks tracked source modifications as `-dirty`, and
reports unavailable revisions as `unknown`. Recollect after changing source
revisions or toolchains. Keeping the input unchanged allows a cached final
program to retain its original timestamp. Changing its contents invalidates
final-program and bootstrap actions, including their binary outputs.

`full_compile_32`, `full_compile_64` and `full_compile_host` now take the
build-information mlstring first. The shared main specifications quantify
over that string and its CakeML representation; their filesystem and
command-line premises are unchanged. `compiler32Prog`, `compiler64X64Prog`
and `compiler64Arm8Prog` bind the concrete string and retain unit entry
points. `compiler$compile` and `compile_correct` are unchanged.
