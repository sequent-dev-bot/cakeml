(*
  Shared translation of the compiler backends and command-line interface.
*)
Theory compiler_commonProg[no_sig_docs]
Ancestors
  from_pancakeProg compiler export ml_translator basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "from_pancakeProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compilerProg");
val _ = ml_translatorLib.use_sub_check true;

val _ = (ml_translatorLib.trace_timing_to
         := SOME "compiler_commonProg_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

Theorem OPT_MMAP_eq_MAP[local]:
  OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs
Proof
  simp [miscTheory.OPT_MMAP_MAP_o]
QED

(* move recursion out of OPT_MMAP to aid the translator *)
val res = panStaticTheory.sh_bd_from_sh_def
  |> REWRITE_RULE [OPT_MMAP_eq_MAP]
  |> SIMP_RULE std_ss [o_DEF]
  |> translate;

val res = translate $ panStaticTheory.sh_bd_from_bd_def;
val res = translate $ panStaticTheory.sh_bd_has_shape_def;
val res = translate $ panStaticTheory.sh_bd_eq_shapes_def;
val res = translate $ panStaticTheory.index_sh_bd_def;
val res = translate $ panStaticTheory.field_sh_bd_def;
val res = translate $ panStaticTheory.based_merge_def;
val res = translate $ panStaticTheory.sh_bd_branch_def;
val res = translate $ panStaticTheory.branch_loc_inf_def;
val res = translate $ panStaticTheory.seq_loc_inf_def;

val res = translate $ panStaticTheory.last_to_str_def;
val res = translate $ panStaticTheory.next_is_reachable_def;
val res = translate $ panStaticTheory.next_now_unreachable_def;
val res = translate $ panStaticTheory.reached_warnable_def;
val res = translate $ panStaticTheory.branch_last_stmt_def;
val res = translate $ panStaticTheory.seq_last_stmt_def;

val res = translate $ panStaticTheory.get_scope_desc_def;
val res = translate $ panStaticTheory.get_scope_msg_def;
val res = translate $ panStaticTheory.get_redec_msg_def;
val res = translate $ panStaticTheory.get_memop_msg_def;
val res = translate $ panStaticTheory.get_oparg_msg_def;
val res = translate $ panStaticTheory.get_unreach_msg_def;
val res = translate $ panStaticTheory.get_rogue_msg_def;
val res = translate $ panStaticTheory.get_non_word_msg_def;
val res = translate $ panStaticTheory.get_shape_mismatch_msg_def;
val res = translate $ panStaticTheory.get_inline_ignore_msg_def;
val res = translate $ panStaticTheory.get_implementation_err_msg_def;

val res = translate $ panStaticTheory.first_repeat_def;
val res = translate $ panStaticTheory.binop_to_str_def;
val res = translate $ panStaticTheory.panop_to_str_def;
val res = translate $ panStaticTheory.primop_to_str_def;
val res = translate $ panStaticTheory.sh_bd_to_str_def;

val res = translate $ panStaticTheory.primitive_idents_def;
val res = translate $ panStaticTheory.add_primitive_hint_def;

val res = translate $ panStaticTheory.check_fun_name_def;
val res = translate $ panStaticTheory.check_global_var_def;
val res = translate $ panStaticTheory.check_local_var_def;
val res = translate $ panStaticTheory.check_redec_var_def;
val res = translate $ panStaticTheory.check_exn_name_def;
val res = translate $ panStaticTheory.check_export_params_def;
val res = translate $ panStaticTheory.check_operands_def;
val res = translate $ panStaticTheory.check_primitive_args_def;
val res = translate $ panStaticTheory.check_func_args_def;
val res = translate $ panStaticTheory.check_struct_fields_def;
val res = translate $ panStaticTheory.check_shape_def;
val res = translate $ panStaticTheory.check_id_shapes_def;

val res = translate $ panStaticTheory.static_check_exp_def;
val res = translate $ panStaticTheory.static_check_prog_def;
val res = translate $ panStaticTheory.static_check_progs_def;
val res = translate $ panStaticTheory.static_check_decls_def;
val res = translate $ INST_TYPE[alpha|->``:staterr``] $
  panStaticTheory.static_check_names_def;
val res = translate $ panStaticTheory.static_check_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "panStaticTheory.static_check_def.");

val res = translate (data_to_wordTheory.max_heap_limit_def
  |> SIMP_RULE std_ss [backend_commonTheory.word_shift_def]);

val r = translate presLangTheory.default_tap_config_def;

val _ = register_type “:any_prog”

val r = backend_passesTheory.to_flat_all_def |> translate;
val r = backend_passesTheory.to_clos_all_def |> translate;
val r = backend_passesTheory.to_bvl_all_def |> translate;
val r = backend_passesTheory.to_bvi_all_def |> translate;

Theorem backend_passes_to_bvi_all_side[local]:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> translate;

val r = backend_passesTheory.word_internal_all_def |> translate;

val r = backend_passesTheory.to_word_all_def
          |> REWRITE_RULE [data_to_wordTheory.stubs_md_def,
                           data_to_wordTheory.stubs_def,APPEND] |> translate;

val r = backend_passesTheory.to_stack_all_def |> translate;

val r = backend_passesTheory.to_lab_all_def |> translate;

val r = backend_passesTheory.to_target_all_def |> translate;

val r = backend_passesTheory.from_lab_all_def |> translate;

val r = backend_passesTheory.from_stack_all_def |> translate;

val r = backend_passesTheory.from_word_all_def |> translate;

val r = backend_passesTheory.from_word_0_all_def |> translate;

val r = presLangTheory.word_to_strs_def |> translate
val r = presLangTheory.stack_to_strs_def |> translate
val r = labLangTheory.Section_num_def |> translate
val r = labLangTheory.Section_metadata_def |> translate
val r = presLangTheory.lab_to_strs_def |> translate

val r = backend_passesTheory.any_prog_pp_def |> translate;
val r = backend_passesTheory.pp_with_title_def |> translate;
val r = backend_passesTheory.compile_tap_def |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "backend_passesTheory.compile_tap_def.");

val r = pan_passesTheory.pan_to_target_all_def
          |> REWRITE_RULE [NULL_EQ] |> translate;

val r = pan_passesTheory.opsize_to_display_def |> translate;
val r = pan_passesTheory.insert_es_def |> translate;
val r = pan_passesTheory.varkind_to_str_def |> translate;
val r = pan_passesTheory.primop_to_display_def |> translate;
val r = pan_passesTheory.pan_exp_to_display_def |> translate;
val r = pan_passesTheory.crep_exp_to_display_def |> translate;
val r = pan_passesTheory.loop_exp_to_display_def |> translate;

val r = pan_passesTheory.dest_annot_def |> translate;
val r = pan_passesTheory.pan_seqs_def |> translate;
val r = pan_passesTheory.crep_seqs_def |> translate;
val r = pan_passesTheory.loop_seqs_def |> translate;
val r = pan_passesTheory.pan_prog_to_display_def |> translate;
val r = pan_passesTheory.crep_prog_to_display_def |> translate;
val r = pan_passesTheory.loop_prog_to_display_def |> translate;
val r = pan_passesTheory.pan_fun_to_display_def |> translate;
val r = pan_passesTheory.crep_fun_to_display_def |> translate;
val r = pan_passesTheory.loop_fun_to_display_def |> translate;
val r = pan_passesTheory.pan_to_strs_def |> translate;
val r = pan_passesTheory.crep_to_strs_def |> translate;
val r = pan_passesTheory.loop_to_strs_def |> translate;
val r = pan_passesTheory.any_pan_prog_pp_def |> translate;
val r = pan_passesTheory.pan_compile_tap_def |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "pan_passesTheory.pan_compile_tap_def.");

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to from_dataProg or something*)
val res = translate all_bytes_eq
val res = translate byte_to_string_eq
val res = translate escape_sym_char_def
val res = translate get_sym_label_def
val res = translate get_sym_labels_def
val res = translate emit_symbol_def
val res = translate emit_symbols_def

Theorem export_byte_to_string_side_total[local]:
  ∀b. export_byte_to_string_side b
Proof
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs []
QED

val _ = update_precondition export_byte_to_string_side_total;

val res = translate split16_def;
val res = translate preamble_def;
val res = translate (data_buffer_def |> CONV_RULE (RAND_CONV EVAL));
val res = translate (code_buffer_def |> CONV_RULE (RAND_CONV EVAL));

(* val res = translate space_line_def; *)

(* TODO: maybe do this directly to the definition of data_section *)
fun is_strcat_lits tm =
let val (t1,t2) = stringSyntax.dest_strcat tm in
  stringSyntax.is_string_literal t1 andalso
              stringSyntax.is_string_literal t2
              end handle HOL_ERR _ => false
fun is_strlit_var tm =
is_var (mlstringSyntax.dest_strlit tm)
       handle HOL_ERR _ => false
val res = translate
          ( data_section_def
              |> SIMP_RULE std_ss [MAP]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT]
              |> SIMP_RULE std_ss [mlstringTheory.strcat_assoc]
              |> SIMP_RULE std_ss [GSYM mlstringTheory.implode_STRCAT]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT])
(* -- *)

val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;

val res = translate words_line_def;

val res = translate word_to_string_def;
(* -- *)

(* compilerTheory *)

val res = translate compilerTheory.find_next_newline_def;

val res = translate compilerTheory.safe_substring_def;

val _ = translate compilerTheory.get_nth_line_def;
val _ = translate compilerTheory.locs_to_string_def;
val _ = translate compilerTheory.ast_locs_to_string_def;
val _ = translate compilerTheory.parse_cml_input_def;
val _ = translate compilerTheory.parse_sexp_input_def;

val res = translate compilerTheory.compile_def;

val res = translate (primTypesTheory.prim_tenv_def
                       |> CONV_RULE (RAND_CONV EVAL));

(* top-level vals must not call functions (no_ptr_eq), so evaluate the
   projections from prim_tenv *)
val res = translate (inferTheory.init_config_def
                     |> CONV_RULE (RAND_CONV EVAL));

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
 *)
val res = translate error_to_str_def;

val res = translate parse_bool_def;
val res = translate parse_num_def;

val res = translate find_str_def;
val res = translate find_strs_def;
val res = translate find_bool_def;
val res = translate find_num_def;
val res = translate get_err_str_def;

val res = translate parse_num_list_def;

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
val res = translate comma_tokens_def;
val res = translate parse_nums_def;

val res = translate clos_knownTheory.default_inline_factor_def;
val res = translate clos_knownTheory.default_max_body_size_def;
val res = translate clos_knownTheory.mk_config_def;
val res = translate parse_clos_conf_def;
val res = translate parse_bvl_conf_def;
val res = translate parse_wtw_conf_def;
val res = translate parse_gc_def;
val res = translate parse_data_conf_def;
val res = translate parse_stack_conf_def;
val res = translate parse_tap_conf_def;
val res = translate parse_lab_conf_def;

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) []);

(* Translations for each target
  Note: ffi_asm is translated multiple times...
 *)

val res = translate backendTheory.prim_src_config_eq;

(* x64 *)
val res = translate x64_configTheory.x64_names_def;
val res = translate export_x64Theory.startup_def;
val res = translate export_x64Theory.ffi_asm_def;
val res = translate export_x64Theory.windows_ffi_asm_def;
val res = translate export_x64Theory.export_func_def;
val res = translate export_x64Theory.export_funcs_def;
val res = translate export_x64Theory.x64_export_def;
val res = translate
          (x64_configTheory.x64_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* riscv *)
val res = translate riscv_configTheory.riscv_names_def;
val res = translate export_riscvTheory.startup_def;
val res = translate export_riscvTheory.ffi_asm_def;
val res = translate export_riscvTheory.export_func_def;
val res = translate export_riscvTheory.export_funcs_def;
val res = translate export_riscvTheory.riscv_export_def;
val res = translate
          (riscv_configTheory.riscv_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* mips *)
val res = translate mips_configTheory.mips_names_def;
val res = translate export_mipsTheory.startup_def;
val res = translate export_mipsTheory.ffi_asm_def;
val res = translate export_mipsTheory.export_func_def;
val res = translate export_mipsTheory.export_funcs_def;
val res = translate export_mipsTheory.mips_export_def;
val res = translate
          (mips_configTheory.mips_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm8 *)
val res = translate arm8_configTheory.arm8_names_def;
val res = translate export_arm8Theory.startup_def;
val res = translate export_arm8Theory.ffi_asm_def;
val res = translate export_arm8Theory.export_func_def;
val res = translate export_arm8Theory.export_funcs_def;
val res = translate (export_arm8Theory.arm8_code_buffer_def
                       |> CONV_RULE (RAND_CONV EVAL));
val res = translate export_arm8Theory.arm8_export_def;
val res = translate
          (arm8_configTheory.arm8_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* ag32 *)
val res = translate ag32_configTheory.ag32_names_def;
val res = translate export_ag32Theory.ag32_export_def;
val res = translate
  (ag32_configTheory.ag32_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm7 *)
(* top-level vals must not call functions (no_ptr_eq), so the register
   name map is evaluated to sptree constructors (as the other targets'
   *_names_def already are) *)
val res = translate (arm7_configTheory.arm7_names_def |> CONV_RULE (RAND_CONV EVAL));
val res = translate export_arm7Theory.startup_def;
val res = translate export_arm7Theory.ffi_asm_def;
val res = translate export_arm7Theory.export_func_def;
val res = translate export_arm7Theory.export_funcs_def;
val res = translate export_arm7Theory.arm7_export_def;
val res = translate
  (arm7_configTheory.arm7_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

(* Rest of the translation *)
val res = translate (extend_conf_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val res = translate parse_target_def;
val res = translate add_tap_output_def;

val res = format_compiler_result_def
            |> Q.GENL[`bytes`,`c`]
            |> Q.ISPECL[`bytes:word8 list`,`c:backend$config`]

            |> translate;

val res = translate backendTheory.ffinames_to_string_list_def;

val res = translate compile_main_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_main_def.");

val res = translate compile_pancake_def;

val res = translate pancake_backend_conf_def;

val res = translate compile_pancake_main_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_pancake_main_def.");

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate (has_help_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate compilerTheory.help_string_def;
val res = translate (newsTheory.query_news_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate parse_pancake_feature_def
val res = translate print_bool_def

Definition nonzero_exit_code_for_error_msg_def:
  nonzero_exit_code_for_error_msg e =
  if compiler$is_error_msg e then
    (let a = empty_ffi «nonzero_exit» in
       ml_translator$force_out_of_memory_error ())
  else ()
End

val res = translate compilerTheory.is_error_msg_def;
val res = translate nonzero_exit_code_for_error_msg_def;

val r = translate (compilerTheory.has_pancake_flag_def
  |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);

Quote add_cakeml:
  fun main_batch (build_info,u) =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_has_help_flag cl then
        print compiler_help_string
      else if compiler_has_version_flag cl then
        print build_info
      else
        case compiler_parse_pancake_feature cl of
          Some rest => print (compiler_print_bool(news_query_news rest))
        | None =>
            if compiler_has_pancake_flag cl then
              case compiler_compile_pancake_main cl (String.explode (TextIO.inputAll (TextIO.openStdIn ())))  of
                (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                           compiler_commonprog_nonzero_exit_code_for_error_msg e)
            else
              case compiler_compile_main cl (String.explode (TextIO.inputAll (TextIO.openStdIn ())))  of
                (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                           compiler_commonprog_nonzero_exit_code_for_error_msg e)
    end
End

val main_batch_v_def = fetch "-" "main_batch_v_def";
val compiler_help_string_v_thm = fetch "-" "compiler_help_string_v_thm";

Theorem main_batch_spec:
   STRING_TYPE build_info build_info_v ∧ IS_SOME (stdin_content fs) ⇒
   app (p:'ffi ffi_proj) main_batch_v
     [Conv NONE [build_info_v; Conv NONE []]] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile build_info (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  rpt strip_tac
  \\ xcf_with_def main_batch_v_def
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto
  >- (
    CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl`
    \\ xsimpl )
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >- (
    fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,PAIR_EQ,option_CASES] )
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac[] \\ rw[]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_fd_content
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [compilerTheory.full_compile_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ irule_at (Pos hd) compiler_help_string_v_thm
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    xapp
    \\ first_assum $ irule_at $ Pos hd
    \\ qexists_tac `fs`
    \\ simp [compilerTheory.full_compile_def]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ Cases_on `parse_pancake_feature (TL cl)`
  \\ gvs [oneline std_preludeTheory.OPTION_TYPE_def]
  >- (
    xmatch
    \\ xlet_auto >- xsimpl
    \\ rename1 `stdin fs source_input stdin_position`
    \\ `stdin_content fs = SOME source_input /\ stdin_position = 0` by (
      gvs [stdin_def,get_fd_content_def]
      \\ fs [stdin_content_def,IS_SOME_EXISTS])
    \\ gvs []
    \\ xif
    >- (
      xlet_auto >- (xcon \\ xsimpl)
      \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
      \\ xlet `POSTv v.
          &STRING_TYPE (implode source_input) v *
          STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
      >- (
        xapp
        \\ qexistsl_tac [`COMMANDLINE cl`,`source_input`,`fs`,`0`]
        \\ fs [STD_streams_get_mode]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ Cases_on `compile_pancake_main (TL cl) source_input`
      \\ rename1 `compile_pancake_main (TL cl) source_input =
                     (compiler_output,compiler_error)`
      \\ gvs [compilerTheory.full_compile_def,ml_translatorTheory.PAIR_TYPE_def]
      \\ xmatch
      \\ xlet_auto >- xsimpl
      \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
      \\ xlet `POSTv uv. &UNIT_TYPE () uv *
          STDIO (add_stderr output_fs compiler_error) * COMMANDLINE cl`
      >- (
        xapp_spec output_stderr_spec
        \\ xsimpl
        \\ qexists_tac `COMMANDLINE cl`
        \\ asm_exists_tac \\ xsimpl
        \\ qexists_tac `output_fs` \\ xsimpl)
      \\ xapp
      \\ asm_exists_tac \\ simp [] \\ xsimpl
    )
    >- (
      xlet_auto >- (xcon \\ xsimpl)
      \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
      \\ xlet `POSTv v.
          &STRING_TYPE (implode source_input) v *
          STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
      >- (
        xapp
        \\ qexistsl_tac [`COMMANDLINE cl`,`source_input`,`fs`,`0`]
        \\ fs [STD_streams_get_mode]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ Cases_on `compile_main (TL cl) source_input`
      \\ rename1 `compile_main (TL cl) source_input =
                     (compiler_output,compiler_error)`
      \\ gvs [compilerTheory.full_compile_def,ml_translatorTheory.PAIR_TYPE_def]
      \\ xmatch
      \\ xlet_auto >- xsimpl
      \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
      \\ xlet `POSTv uv. &UNIT_TYPE () uv *
          STDIO (add_stderr output_fs compiler_error) * COMMANDLINE cl`
      >- (
        xapp_spec output_stderr_spec
        \\ xsimpl
        \\ qexists_tac `COMMANDLINE cl`
        \\ asm_exists_tac \\ xsimpl
        \\ qexists_tac `output_fs` \\ xsimpl)
      \\ xapp
      \\ asm_exists_tac \\ simp [] \\ xsimpl
    )
  )
  >- (
    rename1 `parse_pancake_feature (TL cl) = SOME feature_query`
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ simp [compilerTheory.full_compile_def]
    \\ xapp
    \\ qpat_x_assum `STRING_TYPE (compiler$print_bool _) _` (irule_at (Pos hd))
    \\ qexists_tac `fs`
    \\ xsimpl
  )
QED
