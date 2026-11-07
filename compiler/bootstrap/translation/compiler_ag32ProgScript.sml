(*
  Native AG32 batch entry point for the fused compiler.
*)
Theory compiler_ag32Prog[no_sig_docs]
Ancestors
  compiler_commonProg compilerBuildInfo basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "compiler_commonProg";
val _ = ml_translatorLib.use_sub_check true;
val _ = use_long_names := true;

val _ = next_ml_names := ["compiler_current_build_info_str"];
val res = translate current_build_info_str_def;
val compiler_current_build_info_str_v_thm =
  fetch "-" "compiler_current_build_info_str_v_thm";

Quote add_cakeml:
  fun main u = main_batch (compiler_current_build_info_str,u)
End

val main_v_def = fetch "-" "main_v_def";

Theorem main_spec:
  IS_SOME (stdin_content fs) ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
    (STDIO fs * COMMANDLINE cl)
    (POSTv uv. &UNIT_TYPE () uv *
      STDIO (full_compile current_build_info_str (TL cl) (get_stdin fs) fs) *
      COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp_spec main_batch_spec
  \\ simp [current_build_info_str_def, compiler_current_build_info_str_v_thm]
QED

Theorem main_whole_prog_spec:
  IS_SOME (stdin_content fs) ⇒
   whole_prog_spec main_v cl fs NONE
    ((=) (full_compile current_build_info_str (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp [basis_ffiTheory.whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac `output_fs = _ with numchars := _`
  \\ qexists_tac `output_fs`
  \\ reverse conj_tac
  >- (
    rw [Abbr `output_fs`,compilerTheory.full_compile_def,UNCURRY,
        GSYM fastForwardFD_with_numchars,
        GSYM add_stdo_with_numchars,with_same_numchars]
    \\ PURE_FULL_CASE_TAC
    \\ rw [GSYM fastForwardFD_with_numchars,
           GSYM add_stdo_with_numchars,with_same_numchars,UNCURRY])
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ xsimpl
QED

val sem_thm = prove_sem_thm "main" "compiler_ag32_prog" main_whole_prog_spec;
val compiler_ag32_prog_def = fetch "-" "compiler_ag32_prog_def";

Theorem semantics_compiler_ag32_prog:
  IS_SOME (stdin_content fs) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  sem_satisfies
    (semantics_dec_list
      (init_state (basis_ffi ext cl fs) with
       eval_state :=
         SOME (EvalDecs (eval_state_var with env_id_counter := (0,0,1))))
      init_env compiler_ag32_prog)
    (λbehaviour.
       ∃io_events.
         behaviour = Terminate Success io_events ∧
         extract_fs ext (cl,fs) io_events =
           SOME (full_compile current_build_info_str (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ irule sem_thm
  \\ fs []
QED

val _ = ml_translatorLib.reset_translation(); (* because this translation won't be continued *)
