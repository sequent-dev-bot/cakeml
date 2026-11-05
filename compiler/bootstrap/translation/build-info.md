# Compiler build information

The compiler prints its build information for `--version`. Its timestamp,
CakeML and HOL revisions, and Poly/ML version belong to the final program,
so changing them does not invalidate the compiler correctness proof or
shared compiler translations.

`compilerBuildInfoTheory` reads `compiler_build_info.txt`. Both native
Holmake and holbuild collect this declared input automatically before
building a final compiler program. Holbuild demands the collector only
when a selected target needs the file; compiler correctness and shared
translation targets do not run it.

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
