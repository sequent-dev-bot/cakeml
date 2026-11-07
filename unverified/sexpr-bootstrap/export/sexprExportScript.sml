(*
  Exports the fused compiler S-expression.
*)
Theory sexprExport
Ancestors
  compiler_x64Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_outputs ["cake-sexpr"];

val _ = write_program_def_to_file "cake-sexpr" compiler_x64_prog_def;
