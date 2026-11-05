(*
  Concrete provenance is a final-program input, not a compiler dependency.
*)
Theory compilerBuildInfo
Ancestors
  mlstring
Libs
  preamble

val input = TextIO.openIn "compiler_build_info.txt";
val build_info = TextIO.inputAll input;
val _ = TextIO.closeIn input;

Definition current_build_info_str_def:
  current_build_info_str = strlit ^(stringSyntax.fromMLstring build_info)
End
