(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

section\<open>Dynamic Meta Embedding with Reflection\<close>

theory Generator_dynamic_export_testing
imports Printer
        "../compiler_generic/isabelle_home/src/HOL/Isabelle_Main2"
        "~~/src/HOL/Library/Old_Datatype"
  keywords (* OCL (USE tool) *)
           "Between"
           "Attributes" "Operations" "Constraints"
           "Role"
           "Ordered" "Subsets" "Union" "Redefines" "Derived" "Qualifier"
           "Existential" "Inv" "Pre" "Post"
           (* OCL (added) *)
           "self"
           "Nonunique" "Sequence_"
           "with_only"
           (* Haskabelle *)
           "datatype_old" "datatype_old_atomic" "datatype_old_atomic_sub"
           "try_import" "only_types" "base_path" "ignore_not_in_scope" "abstract_mutual_data_params"
           "concat_modules" "load" "meta"

           (* Isabelle syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION" "SORRY" "no_dirty"
           "deep" "shallow" "syntax_print" "skip_export"
           "generation_semantics"
           "flush_all"

           (* Isabelle semantics (parameterizing the semantics of OCL) *)
           "design" "analysis" "oid_start"

       and (* Isabelle syntax *)
           "generation_syntax"

           :: thy_decl
begin

text\<open>In the ``dynamic'' solution: the exportation is automatically handled inside Isabelle/jEdit.
Inputs are provided using the syntax of OCL, and in output
we basically have two options:
\begin{itemize}
\item The first is to generate an Isabelle file for inspection or debugging.
The generated file can interactively be loaded in Isabelle/jEdit, or saved to the hard disk.
This mode is called the ``deep exportation'' mode or shortly the ``deep'' mode.
The aim is to maximally automate the process one is manually performing in
@{file "Generator_static.thy"}.
\item On the other hand, it is also possible to directly execute
in Isabelle/jEdit the generated file from the random access memory.
This mode corresponds to the ``shallow reflection'' mode or shortly ``shallow'' mode.
\end{itemize}
In both modes, the reflection is necessary since the main part used by both
was defined at Isabelle side.
As a consequence, experimentations in ``deep'' and ``shallow'' are performed
without leaving the editing session, in the same as the one the meta-compiler is actually running.\<close>

apply_code_printing_reflect \<open>
  val stdout_file = Unsynchronized.ref ""
\<close> text\<open>This variable is not used in this theory (only in @{file "Generator_static.thy"}),
       but needed for well typechecking the reflected SML code.\<close>

code_reflect' open META
   functions (* executing the compiler as monadic combinators for deep and shallow *)
             fold_thy_deep fold_thy_shallow

             (* printing the HOL AST to (shallow Isabelle) string *)
             write_file0 write_file

             (* manipulating the compiling environment *)
             compiler_env_config_reset_all
             compiler_env_config_update
             oidInit
             D_output_header_thy_update
             map2_ctxt_term
             check_export_code

             (* printing the input AST to (deep Isabelle) string *)
             isabelle_apply isabelle_of_compiler_env_config

subsection\<open>Interface Between the Reflected and the Native\<close>

ML\<open>
val To_string0 = String.implode o META.to_list
val To_nat = Code_Numeral.integer_of_natural

exception THY_REQUIRED of Position.T
fun get_thy pos f = fn NONE => raise (THY_REQUIRED pos) | SOME thy => f thy

infix 1 #~> |>::
fun f #~> g = uncurry g oo f
fun x |>:: f = cons f x
\<close>

ML\<open>
structure From = struct
 val string = META.SS_base o META.ST
 val binding = string o Binding.name_of
 (*fun term ctxt s = string (YXML.content_of (Syntax.string_of_term ctxt s))*)
 val nat = Code_Numeral.natural_of_integer
 val internal_oid = META.Oid o nat
 val option = Option.map
 val list = List.map
 fun pair f1 f2 (x, y) = (f1 x, f2 y)
 fun pair3 f1 f2 f3 (x, y, z) = (f1 x, f2 y, f3 z)

 structure Pure = struct
 val indexname = pair string nat
 val class = string
 val sort = list class
 fun typ e = (fn
     Type (s, l) => (META.Typea o pair string (list typ)) (s, l)
   | TFree (s, s0) => (META.TFree o pair string sort) (s, s0)
   | TVar (i, s0) => (META.TVara o pair indexname sort) (i, s0)
  ) e
 fun term e = (fn
     Const (s, t) => (META.Consta o pair string typ) (s, t)
   | Free (s, t) => (META.Free o pair string typ) (s, t)
   | Var (i, t) => (META.Var o pair indexname typ) (i, t)
   | Bound i => (META.Bound o nat) i
   | Abs (s, ty, t) => (META.Absa o pair3 string typ term) (s, ty, t)
   | op $ (term1, term2) => (META.Appa o pair term term) (term1, term2)
  ) e
 end

 fun read_term thy expr =
   META.T_pure (Pure.term (Syntax.read_term (get_thy @{here} Proof_Context.init_global thy) expr), SOME (string expr))
end
\<close>

ML\<open>
fun List_mapi f = META.mapi (f o To_nat)
fun out_intensify s1 s2 = Output.state ((s1 |> Markup.markup Markup.intensify) ^ s2)
fun out_intensify' tps fmt = out_intensify (Timing.message (Timing.result tps) |> Markup.markup fmt)

structure Toplevel' = struct
  fun keep_theory f = Toplevel.keep (f o Toplevel.theory_of)
  fun keep f tr = (@{command_keyword print_syntax}, Toplevel.keep f) :: tr
  fun read_write_keep rw = (@{command_keyword print_syntax}, fn tr => tr |> Toplevel.read_write rw |> Toplevel.keep (K ()))
  fun setup_theory (res, tr) f = rev ((@{command_keyword setup}, Toplevel.theory (f res)) :: tr)
  fun keep_output tps fmt msg = cons (@{command_keyword print_syntax}, Toplevel.keep (fn _ => out_intensify' tps fmt msg))
end

structure Resources' = struct
  fun check_path' check_file ctxt dir (name, pos) =
    let
      fun err msg pos = error (msg ^ Position.here pos)
      val _ = Context_Position.report ctxt pos Markup.language_path;
  
      val path = Path.append dir (Path.explode name) handle ERROR msg => err msg pos;
      val path' = Path.expand path handle ERROR msg => err msg pos;
      val _ = Context_Position.report ctxt pos (Markup.path (Path.smart_implode path));
      val _ =
        (case check_file of
          NONE => path
        | SOME check => (check path handle ERROR msg => err msg pos));
    in Path.implode path' end

  fun check_dir thy = check_path' (SOME File.check_dir)
                                  (Proof_Context.init_global thy)
                                  (Resources.master_directory thy)
end
\<close>

ML\<open>
structure Ty' = struct
fun check l_oid l =
  let val Mp = META.map_prod
      val Me = String.explode
      val Mi = String.implode
      val Ml = map in
  META.check_export_code
    (writeln o Mi)
    (warning o Mi)
    (fn s => writeln (Markup.markup (Markup.bad ()) (Mi s)))
    (error o To_string0)
    (Ml (Mp I Me) l_oid)
    ((META.SS_base o META.ST) l)
  end
end
\<close>

subsection\<open>Binding of the Reflected API to the Native API\<close>

ML\<open>
structure META_overload = struct
  val of_semi__typ = META.of_semi_typ To_string0
  val of_semi__term = META.of_semi_terma To_string0
  val of_semi__term' = META.of_semi_term To_string0
  val fold = fold
end
\<close>

ML\<open>
type ('a, 'b) toplevel_dual = { par: 'a, seq: 'b }
type ('transitionM, 'Proof_stateM, 'state) toplevel =
  { context_of: 'state -> local_theory

  , keep: ('state -> unit) -> 'transitionM
  , generic_theory: (generic_theory -> generic_theory) -> 'transitionM
  , theory: (theory -> theory) -> 'transitionM
  , begin_local_theory: bool -> (theory -> local_theory) -> 'transitionM
  , local_theory': (bool * Position.T) option -> (xstring * Position.T) option ->
      (bool -> local_theory -> local_theory) -> 'transitionM
  , local_theory: (bool * Position.T) option -> (xstring * Position.T) option ->
      (local_theory -> local_theory) -> 'transitionM
  , local_theory_to_proof': (bool * Position.T) option -> (xstring * Position.T) option ->
      (bool -> local_theory -> Proof.state) -> 'transitionM
  , local_theory_to_proof: (bool * Position.T) option -> (xstring * Position.T) option ->
      (local_theory -> Proof.state) -> 'transitionM
  , proof': (bool -> Proof.state -> Proof.state) -> 'Proof_stateM
  , proofs: (Proof.state -> Proof.state Seq.result Seq.seq) -> 'Proof_stateM
  , proof: (Proof.state -> Proof.state) -> 'Proof_stateM
  (* *)
  , tr_report: Method.text_range -> 'transitionM -> 'transitionM
  , tr_report_o: Method.text_range option -> 'transitionM -> 'transitionM
  , tr_raw: (Toplevel.transition -> Toplevel.transition) -> 'transitionM
  , pr_report: Method.text_range -> 'Proof_stateM -> 'Proof_stateM
  , pr_report_o: Method.text_range option -> 'Proof_stateM -> 'Proof_stateM
  , dual: (Toplevel.transition -> Toplevel.transition, Proof.state -> Proof.state) toplevel_dual -> 'Proof_stateM }

structure Bind_Isabelle = struct
fun To_binding s = Binding.make (s, Position.none)
val To_sbinding = To_binding o To_string0

fun semi__method_simp g f = Method.Basic (fn ctxt => SIMPLE_METHOD (g (asm_full_simp_tac (f ctxt))))
val semi__method_simp_one = semi__method_simp (fn f => f 1)
val semi__method_simp_all = semi__method_simp (CHANGED_PROP o PARALLEL_GOALS o ALLGOALS)

datatype semi__thm' = Thms_single' of thm
                    | Thms_mult' of thm list

fun semi__thm_attribute ctxt = let open META open META_overload val S = fn Thms_single' t => t in
 fn Thm_thm s => Thms_single' (Proof_Context.get_thm ctxt (To_string0 s))
  | Thm_thms s => Thms_mult' (Proof_Context.get_thms ctxt (To_string0 s))
  | Thm_THEN (e1, e2) =>
      (case (semi__thm_attribute ctxt e1, semi__thm_attribute ctxt e2) of
         (Thms_single' e1, Thms_single' e2) => Thms_single' (e1 RSN (1, e2))
       | (Thms_mult' e1, Thms_mult' e2) => Thms_mult' (e1 RLN (1, e2)))
  | Thm_simplified (e1, e2) =>
      Thms_single' (asm_full_simplify (clear_simpset ctxt addsimps [S (semi__thm_attribute ctxt e2)])
                                      (S (semi__thm_attribute ctxt e1)))
  | Thm_OF (e1, e2) =>
      Thms_single' ([S (semi__thm_attribute ctxt e2)] MRS (S (semi__thm_attribute ctxt e1)))
  | Thm_where (nth, l) =>
      Thms_single' (Rule_Insts.where_rule
                      ctxt
                      (List.map (fn (var, expr) =>
                                   (((To_string0 var, 0), Position.none), of_semi__term expr)) l)
                      []
                      (S (semi__thm_attribute ctxt nth)))
  | Thm_symmetric e1 =>
      let val e2 = S (semi__thm_attribute ctxt (Thm_thm (From.string "sym"))) in
        case semi__thm_attribute ctxt e1 of
          Thms_single' e1 => Thms_single' (e1 RSN (1, e2))
        | Thms_mult' e1 => Thms_mult' (e1 RLN (1, [e2]))
      end
  | Thm_of (nth, l) =>
      Thms_single' (Rule_Insts.of_rule
                     ctxt
                     (List.map (SOME o of_semi__term) l, [])
                     []
                     (S (semi__thm_attribute ctxt nth)))
end

fun semi__thm_attribute_single ctxt s = case (semi__thm_attribute ctxt s) of Thms_single' t => t

fun semi__thm_mult ctxt =
  let fun f thy = case (semi__thm_attribute ctxt thy) of Thms_mult' t => t
                                                  | Thms_single' t => [t] in
  fn META.Thms_single thy => f thy
   | META.Thms_mult thy => f thy
  end

fun semi__thm_mult_l ctxt l = List.concat (map (semi__thm_mult ctxt) l)

fun semi__method_simp_only l ctxt = clear_simpset ctxt addsimps (semi__thm_mult_l ctxt l)
fun semi__method_simp_add_del_split (l_add, l_del, l_split) ctxt =
  fold Splitter.add_split (semi__thm_mult_l ctxt l_split)
                          (ctxt addsimps (semi__thm_mult_l ctxt l_add)
                                delsimps (semi__thm_mult_l ctxt l_del))

fun semi__method expr = let open META open Method open META_overload in case expr of
    Method_rule o_s => Basic (fn ctxt =>
      METHOD (HEADGOAL o Classical.rule_tac
                           ctxt
                           (case o_s of NONE => []
                                      | SOME s => [semi__thm_attribute_single ctxt s])))
  | Method_drule s => Basic (fn ctxt => drule ctxt 0 [semi__thm_attribute_single ctxt s])
  | Method_erule s => Basic (fn ctxt => erule ctxt 0 [semi__thm_attribute_single ctxt s])
  | Method_elim s => Basic (fn ctxt => elim ctxt [semi__thm_attribute_single ctxt s])
  | Method_intro l => Basic (fn ctxt => intro ctxt (map (semi__thm_attribute_single ctxt) l))
  | Method_subst (asm, l, s) => Basic (fn ctxt =>
      SIMPLE_METHOD' ((if asm then EqSubst.eqsubst_asm_tac else EqSubst.eqsubst_tac)
                        ctxt
                        (map (the o Int.fromString o To_string0) l)
                        [semi__thm_attribute_single ctxt s]))
  | Method_insert l => Basic (fn ctxt => insert (semi__thm_mult_l ctxt l))
  | Method_plus t => Combinator ( no_combinator_info
                                , Repeat1
                                , [Combinator (no_combinator_info, Then, List.map semi__method t)])
  | Method_option t => Combinator ( no_combinator_info
                                  , Try
                                  , [Combinator (no_combinator_info, Then, List.map semi__method t)])
  | Method_or t => Combinator (no_combinator_info, Orelse, List.map semi__method t)
  | Method_one (Method_simp_only l) => semi__method_simp_one (semi__method_simp_only l)
  | Method_one (Method_simp_add_del_split l) => semi__method_simp_one (semi__method_simp_add_del_split l)
  | Method_all (Method_simp_only l) => semi__method_simp_all (semi__method_simp_only l)
  | Method_all (Method_simp_add_del_split l) => semi__method_simp_all (semi__method_simp_add_del_split l)
  | Method_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (fold (fn (f, l) => fold f l)
              [(Simplifier.add_simp, semi__thm_mult_l ctxt l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string0) l_split)]
              ctxt)))
  | Method_rename_tac l => Basic (K (SIMPLE_METHOD' (Tactic.rename_tac (List.map To_string0 l))))
  | Method_case_tac e =>
      Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (of_semi__term e) [] NONE))
  | Method_blast n =>
      Basic (case n of NONE => SIMPLE_METHOD' o blast_tac
                     | SOME lim => fn ctxt => SIMPLE_METHOD' (depth_tac ctxt (To_nat lim)))
  | Method_clarify => Basic (fn ctxt => (SIMPLE_METHOD' (fn i => CHANGED_PROP (clarify_tac ctxt i))))
  | Method_metis (l_opt, l) =>
      Basic (fn ctxt => (METHOD oo Metis_Tactic.metis_method)
                          ( (if l_opt = [] then NONE else SOME (map To_string0 l_opt), NONE)
                          , map (semi__thm_attribute_single ctxt) l)
                          ctxt)
end

fun then_tactic l = let open Method in
  (Combinator (no_combinator_info, Then, map semi__method l), (Position.none, Position.none))
end

fun terminal_proof0 f1 f2 f3 top o_by = let open META in case o_by of
   Command_done =>       (@{command_keyword done}, #dual top { par = Isar_Cmd.done_proof
                                                             , seq = f1 })
 | Command_sorry =>      (@{command_keyword sorry}, #dual top { par = Isar_Cmd.skip_proof
                                                              , seq = f2 true })
 | Command_by l_apply => (@{command_keyword by}, let val (m1, m2) = (then_tactic l_apply, NONE) in
                                                 #pr_report top m1
                                                   (#pr_report_o top m2
                                                     (#dual top { par = Isar_Cmd.terminal_proof (m1, m2)
                                                                , seq = f3 (m1, m2) })) end)
end

fun terminal_proof_dual top =
  terminal_proof0 Proof.local_done_proof Proof.local_skip_proof Proof.local_terminal_proof top

fun proof_show_gen top f (thes, thes_when) st = st
  |>:: (@{command_keyword proof},
      let val m = SOME ( Method.Source [Token.make_string ("-", Position.none)]
                       , (Position.none, Position.none)) in
      (#pr_report_o top m (#proofs top (Proof.proof m))) end)
  |> f
  |>:: (@{command_keyword show}, #proof' top (fn int => Proof.show_cmd
       (thes_when = [])
       NONE
       (K I)
       []
       (if thes_when = [] then [] else [(Binding.empty_atts, map (fn t => (t, [])) thes_when)])
       [(Binding.empty_atts, [(thes, [])])]
       int #> #2))

fun semi__command_state top (META.Command_apply_end l) = let open META_overload in
  cons (@{command_keyword apply_end}, let val m = then_tactic l in
    #pr_report top m (#proofs top (Proof.apply_end m)) end)
end

fun semi__command_proof top = let open META_overload
  val thesis = "?thesis"
  fun cons_proof_show f = proof_show_gen top f (thesis, [])
  fun cons_let (e1, e2) =
        cons (@{command_keyword let}, #proof top
          (Proof.let_bind_cmd [([of_semi__term e1], of_semi__term e2)])) in
  fn META.Command_apply l =>
        cons (@{command_keyword apply}, let val m = then_tactic l in
          #pr_report top m (#proofs top (Proof.apply m)) end)
   | META.Command_using l =>
        cons (@{command_keyword using}, #proof top (fn st =>
          Proof.using [map (fn s => ([s], [])) (semi__thm_mult_l (Proof.context_of st) l)] st))
   | META.Command_unfolding l =>
        cons (@{command_keyword unfolding}, #proof top (fn st =>
          Proof.unfolding [map (fn s => ([s], [])) (semi__thm_mult_l (Proof.context_of st) l)] st))
   | META.Command_let e =>
        cons_proof_show (cons_let e)
   | META.Command_have (n, b, e, e_pr) => (fn st => st
     |> cons_proof_show (fn st => st
       |>:: (@{command_keyword have}, #proof' top (fn int =>
          Proof.have_cmd true NONE (K I) [] []
            [( (To_sbinding n, if b then [[Token.make_string ("simp", Position.none)]] else [])
             , [(of_semi__term e, [])])] int #> #2))
       |>:: terminal_proof_dual top e_pr))
   | META.Command_fix_let (l, l_let, o_exp, _) => (fn st => st
     |> proof_show_gen top (fn st => st
       |>:: (@{command_keyword fix}, #proof top
            (Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l)))
       |> fold cons_let l_let)
          ( case o_exp of NONE => thesis | SOME (l_spec, _) =>
             (String.concatWith (" \<Longrightarrow> ")
                                (List.map of_semi__term l_spec))
          , case o_exp of NONE => [] | SOME (_, l_when) => List.map of_semi__term l_when))
end

fun end' top =
 (@{command_keyword end}, #tr_raw top (Toplevel.exit o Toplevel.end_local_theory o Toplevel.close_target o
                                       Toplevel.end_proof (K Proof.end_notepad)))

structure Cmd = struct open META open META_overload
fun input_source ml = Input.source false (of_semi__term' ml) (Position.none, Position.none)

fun datatype' top (Datatypea (version, l)) = 
  case version of Datatype_new => #local_theory top NONE NONE
  (BNF_FP_Def_Sugar.co_datatype_cmd
    BNF_Util.Least_FP
    BNF_LFP.construct_lfp
    (Ctr_Sugar.default_ctr_options_cmd,
     (map (fn ((n, v), l) =>
            ( ( ( ((map (fn v => (SOME (To_binding ""), (To_string0 v, NONE))) v, To_sbinding n), NoSyn)
                , List.map (fn (n, l) => ( ( (To_binding "", To_sbinding n)
                                           , List.map (fn s => (To_binding "", of_semi__typ s)) l)
                                         , NoSyn)) l)
              , (To_binding "", To_binding "", To_binding ""))
            , [])) l)))
  | _ => #theory top
  ((snd oo Old_Datatype.add_datatype_cmd
     (Old_Datatype_Aux.default_config'
       (case version of Datatype_old => 0 | Datatype_old_atomic => 1 | _ => 2)))
    (map (fn ((n, v), l) =>
           ( (To_sbinding n, map (fn v => (To_string0 v, NONE)) v, NoSyn)
           , List.map (fn (n, l) => (To_sbinding n, List.map of_semi__typ l, NoSyn)) l))
         l))

fun type_synonym top (Type_synonym ((n, v), l)) = #theory top (fn thy => let val s_bind = To_sbinding n in
  (snd o Typedecl.abbrev_global
           (s_bind, map To_string0 v, NoSyn)
           (Isabelle_Typedecl.abbrev_cmd0 (SOME s_bind) thy (of_semi__typ l))) thy end)
fun type_notation top (Type_notation (n, e)) = #local_theory top NONE NONE
  (Specification.type_notation_cmd true ("", true) [(To_string0 n, Mixfix (Input.string (To_string0 e), [], 1000, Position.no_range))])
fun instantiation1 name thy = thy
  |> Class.instantiation ([ let val Term.Type (s, _) = Isabelle_Typedecl.abbrev_cmd0 NONE thy name in s end ],
                          [],
                          Syntax.read_sort (Proof_Context.init_global thy) "object")
fun instantiation2 name n_def expr =
  Specification.definition_cmd NONE [] [] ( (To_binding (To_string0 n_def ^ "_" ^ name ^ "_def"), [])
                                          , of_semi__term expr)
fun overloading1 n_c e_c = Overloading.overloading_cmd [(To_string0 n_c, of_semi__term e_c, true)]
fun overloading2 n e =
  #2 oo Specification.definition_cmd NONE [] [] ((To_sbinding n, []), of_semi__term e)
fun consts top (Consts (n, ty, symb)) = #theory top
  (Sign.add_consts_cmd [( To_sbinding n
                        , of_semi__typ ty
                        , Mixfix (Input.string ("(_) " ^ To_string0 symb), [], 1000, Position.no_range))])
fun definition top def = #local_theory' top NONE NONE
  let val (def, e) = case def of
      Definitiona e => (NONE, e)
    | Definition_where1 (name, (abbrev, prio), e) =>
        (SOME ( To_sbinding name
              , NONE
              , Mixfix (Input.string ("(1" ^ of_semi__term abbrev ^ ")"), [], To_nat prio, Position.no_range)), e)
    | Definition_where2 (name, abbrev, e) =>
        (SOME ( To_sbinding name
              , NONE
              , Mixfix (Input.string ("(" ^ of_semi__term abbrev ^ ")"), [], 1000, Position.no_range)), e) in fn ctxt => ctxt
  |> #2 oo Specification.definition_cmd def [] [] (Binding.empty_atts, of_semi__term e) end
fun lemmas top lemmas = #local_theory' top NONE NONE (fn disp => fn lthy =>
  let val (simp, s, l) =
    case lemmas of Lemmas_simp_thm (simp, s, l) =>
                     (simp, s, map (fn x => ([semi__thm_attribute_single lthy x], [])) l)
                 | Lemmas_simp_thms (s, l) =>
                     (true, s, map (fn x => (Proof_Context.get_thms lthy (To_string0 x), [])) l) in
  (#2 o Specification.theorems Thm.theoremK
    [((To_sbinding s, List.map (fn s => Attrib.check_src lthy [Token.make_string (s, Position.none)])
                               (if simp then ["simp", "code_unfold"] else [])),
      l)]
    []
    disp) lthy end)
fun lemma1 n l_spec = Specification.theorem_cmd true Thm.theoremK NONE (K I)
  Binding.empty_atts [] [] (Element.Shows [((To_sbinding n, [])
                                            ,[((String.concatWith (" \<Longrightarrow> ")
                                                  (List.map of_semi__term l_spec)), [])])])
fun lemma1' n l_spec concl = Specification.theorem_cmd true Thm.theoremK NONE (K I)
  (To_sbinding n, [])
  []
  (List.map (fn (n, (b, e)) =>
              Element.Assumes [( ( To_sbinding n
                                 , if b then [[Token.make_string ("simp", Position.none)]] else [])
                               , [(of_semi__term e, [])])])
            l_spec)
  (Element.Shows [(Binding.empty_atts,[(of_semi__term concl, [])])])
fun lemma3 l_apply = map_filter (fn META.Command_let _ => SOME []
                                  | META.Command_have _ => SOME []
                                  | META.Command_fix_let (_, _, _, l) => SOME l
                                  | _ => NONE)
                                (rev l_apply)
fun axiomatization top (Axiomatization (n, e)) = #theory top
  (#2 o Specification.axiomatization_cmd [] [] [] [((To_sbinding n, []), of_semi__term e)])
fun section n s _ =
  let fun mk s n = if n <= 0 then s else mk ("  " ^ s) (n - 1) in
    out_intensify (mk (Markup.markup Markup.keyword3 (To_string0 s)) n) ""
  end
fun ml top (SMLa ml) = #generic_theory top
  (ML_Context.exec let val source = input_source ml in
                   fn () => ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source
                   end #>
    Local_Theory.propagate_ml_env)
fun setup top (Setup ml) = #theory top (Isar_Cmd.setup (input_source ml))
fun thm top (Thm thm) = #keep top (fn state =>
  let val lthy = #context_of top state in
    Print_Mode.with_modes [] (fn () => writeln
      (Pretty.string_of
        (Proof_Context.pretty_fact lthy ("", List.map (semi__thm_attribute_single lthy) thm)))) ()
  end)
fun interpretation1 n loc_n loc_param =
  Interpretation.interpretation_cmd ( [ ( (To_string0 loc_n, Position.none)
                                        , ( (To_string0 n, true)
                                          , if loc_param = [] then
                                              Expression.Named []
                                            else
                                              Expression.Positional (map (SOME o of_semi__term)
                                                                         loc_param)))]
                                    , [])
                                    []
end

structure Command_Transition = struct

fun semi__theory (top : ('transitionM, 'transitionM, 'state) toplevel) = let open META open META_overload
 in (*let val f = *)fn
  Theory_datatype datatype' =>
  cons (@{command_keyword datatype}, Cmd.datatype' top datatype')
| Theory_type_synonym type_synonym => (*Toplevel.local_theory*)
  cons (@{command_keyword type_synonym}, Cmd.type_synonym top type_synonym)
| Theory_type_notation type_notation =>
  cons (@{command_keyword type_notation}, Cmd.type_notation top type_notation)
| Theory_instantiation (Instantiation (n, n_def, expr)) => let val name = To_string0 n in fn acc => acc
  |>:: (@{command_keyword instantiation}, #begin_local_theory top true (Cmd.instantiation1 name))
  |>:: (@{command_keyword definition}, #local_theory' top NONE NONE (#2 oo Cmd.instantiation2 name n_def expr))
  |>:: (@{command_keyword instance}, #local_theory_to_proof top NONE NONE (Class.instantiation_instance I))
  |>:: (@{command_keyword ".."}, #tr_raw top Isar_Cmd.default_proof)
  |>:: end' top end
| Theory_overloading (Overloading (n_c, e_c, n, e)) => (fn acc => acc
  |>:: (@{command_keyword overloading}, #begin_local_theory top true (Cmd.overloading1 n_c e_c))
  |>:: (@{command_keyword definition}, #local_theory' top NONE NONE (Cmd.overloading2 n e))
  |>:: end' top)
| Theory_consts consts =>
  cons (@{command_keyword consts}, Cmd.consts top consts)
| Theory_definition definition =>
  cons (@{command_keyword definition}, Cmd.definition top definition)
| Theory_lemmas lemmas =>
  cons (@{command_keyword lemmas}, Cmd.lemmas top lemmas)
| Theory_lemma (Lemma (n, l_spec, l_apply, o_by)) => (fn acc => acc
  |>:: (@{command_keyword lemma}, #local_theory_to_proof' top NONE NONE (Cmd.lemma1 n l_spec))
  |> fold (semi__command_proof top o META.Command_apply) l_apply
  |>:: terminal_proof_dual top o_by)
| Theory_lemma (Lemma_assumes (n, l_spec, concl, l_apply, o_by)) => (fn acc => acc
  |>:: (@{command_keyword lemma}, #local_theory_to_proof' top NONE NONE (Cmd.lemma1' n l_spec concl))
  |> fold (semi__command_proof top) l_apply
  |> (fn st => st
    |>:: terminal_proof_dual top o_by
    |> (case Cmd.lemma3 l_apply of
        [] => I
      | _ :: l =>
        let fun cons_qed m =
  cons (@{command_keyword qed}, #tr_report_o top m (#tr_raw top (Isar_Cmd.qed m))) in fn st => st
        |> fold (fn l => fold (semi__command_state top) l o cons_qed NONE) l
        |> cons_qed NONE end)))
| Theory_axiomatization axiomatization =>
  cons (@{command_keyword axiomatization}, Cmd.axiomatization top axiomatization)
| Theory_section (Section (n, s)) => let val n = To_nat n in fn st => st
  |>:: (case n of 0 =>
        @{command_keyword section} | 1 =>
        @{command_keyword subsection} | _ =>
        @{command_keyword subsubsection},
     #tr_raw top (Thy_Output.document_command {markdown = false} (NONE, Input.string (To_string0 s))))
  |>:: (@{command_keyword print_syntax}, #keep top (Cmd.section n s)) end
| Theory_text (Text s) =>
  cons (@{command_keyword text},
     #tr_raw top (Thy_Output.document_command {markdown = true} (NONE, Input.string (To_string0 s))))
| Theory_text_raw (Text_raw s) =>
  cons (@{command_keyword text_raw},
     #tr_raw top (Thy_Output.document_command {markdown = true} (NONE, Input.string (To_string0 s))))
| Theory_ML ml =>
  cons (@{command_keyword ML}, Cmd.ml top ml)
| Theory_setup setup =>
  cons (@{command_keyword setup}, Cmd.setup top setup)
| Theory_thm thm =>
  cons (@{command_keyword thm}, Cmd.thm top thm)
| Theory_interpretation (Interpretation (n, loc_n, loc_param, o_by)) => (fn st => st
  |>:: (@{command_keyword interpretation}, #local_theory_to_proof top NONE NONE
     (Cmd.interpretation1 n loc_n loc_param))
  |>:: terminal_proof_dual top o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end
end

structure Command_Theory = struct

fun local_terminal_proof o_by = let open META in case o_by of
   Command_done => Proof.local_done_proof
 | Command_sorry => Proof.local_skip_proof true
 | Command_by l_apply => Proof.local_terminal_proof (then_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open META in case o_by of
   Command_done => Proof.global_done_proof
 | Command_sorry => Proof.global_skip_proof true
 | Command_by l_apply => Proof.global_terminal_proof (then_tactic l_apply, NONE)
end

fun semi__command_state' top pr = fold snd (rev (semi__command_state top pr []))
fun semi__command_proof' top pr = fold snd (rev (semi__command_proof top pr []))

fun semi__theory top = let open META open META_overload in (*let val f = *)fn
  Theory_datatype datatype' => Cmd.datatype' top datatype'
| Theory_type_synonym type_synonym => Cmd.type_synonym top type_synonym
| Theory_type_notation type_notation => Cmd.type_notation top type_notation
| Theory_instantiation (Instantiation (n, n_def, expr)) => #theory top (fn thy => let val name = To_string0 n in thy
  |> Cmd.instantiation1 name
  |> (fn thy => let val ((_, (_, ty)), thy) = Cmd.instantiation2 name n_def expr false thy in ([ty], thy) end)
  |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn ctxt => fn thms =>
       Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms))
  |-> K I end)
| Theory_overloading (Overloading (n_c, e_c, n, e)) => #theory top (fn thy => thy
  |> Cmd.overloading1 n_c e_c
  |> Cmd.overloading2 n e false
  |> Local_Theory.exit_global)
| Theory_consts consts => Cmd.consts top consts
| Theory_definition definition => Cmd.definition top definition
| Theory_lemmas lemmas => Cmd.lemmas top lemmas
| Theory_lemma (Lemma (n, l_spec, l_apply, o_by)) => #local_theory top NONE NONE (fn lthy => lthy
  |> Cmd.lemma1 n l_spec false
  |> fold (semi__command_proof' top o META.Command_apply) l_apply
  |> global_terminal_proof o_by)
| Theory_lemma (Lemma_assumes (n, l_spec, concl, l_apply, o_by)) => #local_theory top NONE NONE (fn lthy => lthy
  |> Cmd.lemma1' n l_spec concl false
  |> fold (semi__command_proof' top) l_apply
  |> (case Cmd.lemma3 l_apply of
        [] => global_terminal_proof o_by
      | _ :: l => let val arg = (NONE, true) in fn st => st
        |> local_terminal_proof o_by
        |> fold (fn l => fold (semi__command_state' top) l o Proof.local_qed arg) l
        |> Proof.global_qed arg end))
| Theory_axiomatization axiomatization => Cmd.axiomatization top axiomatization
| Theory_section (Section (n, s)) => #keep top (Cmd.section (To_nat n) s)
| Theory_text _ => #keep top (K ())
| Theory_text_raw _ => #keep top (K ())
| Theory_ML ml => Cmd.ml top ml
| Theory_setup setup => Cmd.setup top setup
| Theory_thm thm => Cmd.thm top thm
| Theory_interpretation (Interpretation (n, loc_n, loc_param, o_by)) => #local_theory top NONE NONE (fn lthy => lthy
  |> Cmd.interpretation1 n loc_n loc_param
  |> global_terminal_proof o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end
end

end

structure Bind_META = struct open Bind_Isabelle

local
  open META
  open META_overload

  fun semi__locale data thy = thy
           |> (   Expression.add_locale_cmd
                    (To_sbinding (META.holThyLocale_name data))
                    Binding.empty
                    ([], [])
                    (List.concat
                      (map
                        (fn (fixes, assumes) => List.concat
                          [ map (fn (e,ty) => Element.Fixes [( To_binding (of_semi__term e)
                                                             , SOME (of_semi__typ ty)
                                                             , NoSyn)]) fixes
                          , case assumes of NONE => []
                                          | SOME (n, e) => [Element.Assumes [( (To_sbinding n, [])
                                                                             , [(of_semi__term e, [])])]]])
                        (META.holThyLocale_header data)))
               #> #2)

  fun semi__aux thy =
    map2_ctxt_term
      (fn T_pure x => T_pure x
        | e =>
          let fun aux e = case e of
            T_to_be_parsed (s, _) => SOME let val t = Syntax.read_term (get_thy @{here} Proof_Context.init_global thy)
                                                                       (To_string0 s) in
                                          (t, s, Term.add_frees t [])
                                          end
          | T_lambda (a, e) =>
            Option.map
              (fn (e, s, l_free) =>
               let val a0 = To_string0 a
                   val (t, l_free) = case List.partition (fn (x, _) => x = a0) l_free of
                                       ([], l_free) => (Term.TFree ("'a", ["HOL.type"]), l_free)
                                     | ([(_, t)], l_free) => (t, l_free) in
               (lambda ( Term.Free (a0, t)) e
                       , META.String_concatWith (From.string "", [From.string "(% ", a, From.string ". ", s, From.string ")"])
                       , l_free)
               end)
              (aux e)
          | _ => NONE in
          case aux e of
            NONE => error "nested pure expression not expected"
          | SOME (e, s, _) => META.T_pure (From.Pure.term e, SOME s)
          end)
in

fun all_meta_tr top aux ret = fn
  META_semi_theories thy => ret o
    (case thy of
       Theories_one thy => Command_Transition.semi__theory top thy
     | Theories_locale (data, l) => fn acc => acc
       |>:: (@{command_keyword locale}, #begin_local_theory top true (semi__locale data))
       |> fold (fold (Command_Transition.semi__theory top)) l
       |>:: end' top)
| META_boot_generation_syntax _ => ret o I
| META_boot_setup_env _ => ret o I
| META_all_meta_embedding meta => aux (semi__aux NONE meta)

fun all_meta_thy top_theory top_local_theory aux ret = fn
  META_semi_theories thy => ret o
    (case thy of
       Theories_one thy => Command_Theory.semi__theory top_theory thy
     | Theories_locale (data, l) => (*Toplevel.begin_local_theory*) fn thy => thy
       |> semi__locale data
       |> fold (fold (Command_Theory.semi__theory top_local_theory)) l
       |> Local_Theory.exit_global)
| META_boot_generation_syntax _ => ret o I
| META_boot_setup_env _ => ret o I
| META_all_meta_embedding meta => fn thy => aux (semi__aux (SOME thy) meta) thy
end
end
\<close>

subsection\<open>Directives of Compilation for Target Languages\<close>

ML\<open>
structure Deep0 = struct

fun apply_hs_code_identifiers ml_module thy =
  let fun mod_hs (fic, ml_module) = Code_Symbol.Module (fic, [("Haskell", SOME ml_module)]) in
  fold (Code_Target.set_identifiers o mod_hs)
    (map (fn x => (Context.theory_name x, ml_module))
         (* list of .hs files that will be merged together in "ml_module" *)
         ( thy
           :: (* we over-approximate the set of compiler files *)
              Context.ancestors_of thy)) thy end

structure Export_code_env = struct
  structure Isabelle = struct
    val function = "write_file"
    val argument_main = "main"
  end

  structure Haskell = struct
    val function = "Function"
    val argument = "Argument"
    val main = "Main"
    structure Filename = struct
      fun hs_function ext = function ^ "." ^ ext
      fun hs_argument ext = argument ^ "." ^ ext
      fun hs_main ext = main ^ "." ^ ext
    end
  end

  structure OCaml = struct
    val make = "write"
    structure Filename = struct
      fun function ext = "function." ^ ext
      fun argument ext = "argument." ^ ext
      fun main_fic ext = "main." ^ ext
      fun makefile ext = make ^ "." ^ ext
    end
  end

  structure Scala = struct
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
    end
  end

  structure SML = struct
    val main = "Run"
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
      fun stdout ext = "Stdout." ^ ext
      fun main_fic ext = main ^ "." ^ ext
    end
  end

  datatype file_input = File
                      | Directory
end

fun compile l cmd =
  let val (l, rc) = fold (fn cmd => (fn (l, 0) =>
                                         let val {out, err, rc, ...} = Bash.process cmd in
                                         ((out, err) :: l, rc) end
                                     | x => x)) l ([], 0)
      val l = rev l in
  if rc = 0 then
    (l, Isabelle_System.bash_output cmd)
  else
    let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
    error "Compilation failed"
    end
  end

val check =
  fold (fn (cmd, msg) => fn () =>
    let val (out, rc) = Isabelle_System.bash_output cmd in
    if rc = 0 then
      ()
    else
      ( writeln out
      ; error msg)
    end)

val compiler = let open Export_code_env in
  [ let val ml_ext = "hs" in
    ( "Haskell", ml_ext, Directory, Haskell.Filename.hs_function
    , check [("ghc --version", "ghc is not installed (required for compiling a Haskell project)")]
    , (fn mk_fic => fn _ => fn mk_free => fn thy =>
        File.write (mk_fic ("Main." ^ ml_ext))
          (String.concatWith "; " [ "import qualified Unsafe.Coerce"
                         , "import qualified " ^ Haskell.function
                         , "import qualified " ^ Haskell.argument
                         , "main :: IO ()"
                         , "main = " ^ Haskell.function ^ "." ^ Isabelle.function ^
                           " (Unsafe.Coerce.unsafeCoerce " ^ Haskell.argument ^ "." ^
                           mk_free (Proof_Context.init_global thy)
                                   Isabelle.argument_main ([]: (string * string) list) ^
                           ")"]))
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ "/" ^ Haskell.Filename.hs_argument ml_ext ^ " " ^
                          Path.implode tmp_export_code
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ghc -outputdir _build " ^ Haskell.Filename.hs_main ml_ext ]
                (Path.implode (Path.append tmp_export_code (Path.make [Haskell.main]))))
    end
  , let val ml_ext = "ml" in
    ( "OCaml", ml_ext, File, OCaml.Filename.function
    , check [("ocp-build -version", "ocp-build is not installed (required for compiling an OCaml project)")
            ,("ocamlopt -version", "ocamlopt is not installed (required for compiling an OCaml project)")]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
        let val () =
          File.write
            (mk_fic (OCaml.Filename.makefile "ocp"))
            (String.concat
              [ "comp += \"-g\" link += \"-g\" "
              , "begin generated = true begin library \"nums\" end end "
              , "begin program \"", OCaml.make, "\" sort = true files = [ \"", OCaml.Filename.function ml_ext
              , "\" \"", OCaml.Filename.argument ml_ext
              , "\" \"", OCaml.Filename.main_fic ml_ext
              , "\" ]"
              , "requires = [\"nums\"] "
              , "end" ]) in
        File.write (mk_fic (OCaml.Filename.main_fic ml_ext))
          ("let _ = Function." ^ ml_module ^ "." ^ Isabelle.function ^
           " (Obj.magic (Argument." ^ ml_module ^ "." ^
           mk_free (Proof_Context.init_global thy)
                   Isabelle.argument_main
                   ([]: (string * string) list) ^ "))")
        end
    , fn tmp_export_code => fn tmp_file =>
        compile
          [ "mv " ^ tmp_file ^ " " ^
              Path.implode (Path.append tmp_export_code (Path.make [OCaml.Filename.argument ml_ext]))
          , "cd " ^ Path.implode tmp_export_code ^
            " && ocp-build -init -scan -no-bytecode 2>&1" ]
          (Path.implode (Path.append tmp_export_code (Path.make [ "_obuild"
                                                                , OCaml.make
                                                                , OCaml.make ^ ".asm"]))))
    end
  , let val ml_ext = "scala"
        val ml_module = Unsynchronized.ref ("", "") in
    ( "Scala", ml_ext, File, Scala.Filename.function
    , check [("scala -e 0", "scala is not installed (required for compiling a Scala project)")]
    , (fn _ => fn ml_mod => fn mk_free => fn thy =>
        ml_module := (ml_mod, mk_free (Proof_Context.init_global thy)
                                      Isabelle.argument_main
                                      ([]: (string * string) list)))
    , fn tmp_export_code => fn tmp_file =>
        let val l = File.read_lines (Path.explode tmp_file)
            val (ml_module, ml_main) = Unsynchronized.! ml_module
            val () =
              File.write_list
               (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext]))
               (List.map
                 (fn s => s ^ "\n")
                 ("object " ^ ml_module ^ " { def main (__ : Array [String]) = " ^
                  ml_module ^ "." ^ Isabelle.function ^ " (" ^ ml_module ^ "." ^ ml_main ^ ")"
                  :: l @ ["}"])) in
        compile []
          ("scala -nowarn " ^ Path.implode (Path.append tmp_export_code
                                                        (Path.make [Scala.Filename.argument ml_ext])))
        end)
    end
  , let val ml_ext_thy = "thy"
        val ml_ext_ml = "ML" in
    ( "SML", ml_ext_ml, File, SML.Filename.function
    , check [ let open Path val isa = "isabelle" in
              ( implode (expand (append (variable "ISABELLE_HOME") (make ["bin", isa]))) ^ " version"
              , isa ^ " is not installed (required for compiling a SML project)")
              end ]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val esc_star = "*"
             fun ml l =
               List.concat
               [ [ "ML{" ^ esc_star ]
               , map (fn s => s ^ ";") l
               , [ esc_star ^ "}"] ]
             val () =
               let val fic = mk_fic (SML.Filename.function ml_ext_ml) in
               (* replace ("\\" ^ "<") by ("\\\060") in 'fic' *)
               File.write_list fic
                 (map (fn s =>
                         (if s = "" then
                           ""
                         else
                           String.concatWith "\\"
                             (map (fn s =>
                                     let val l = String.size s in
                                     if l > 0 andalso String.sub (s,0) = #"<" then
                                       "\\060" ^ String.substring (s, 1, String.size s - 1)
                                     else
                                       s end)
                                  (String.fields (fn c => c = #"\\") s))) ^ "\n")
                      (File.read_lines fic))
               end in
         File.write_list (mk_fic (SML.Filename.main_fic ml_ext_thy))
           (map (fn s => s ^ "\n") (List.concat
             [ [ "theory " ^ SML.main
               , "imports Main"
               , "begin"
               , "declare [[ML_print_depth = 500]]"
                 (* any large number so that @{make_string} displays all the expression *) ]
             , ml [ "val stdout_file = Unsynchronized.ref (File.read (Path.make [\"" ^
                      SML.Filename.stdout ml_ext_ml ^ "\"]))"
                  , "use \"" ^ SML.Filename.argument ml_ext_ml ^ "\"" ]
             , ml let val arg = "argument" in
                  [ "val " ^ arg ^ " = YXML.content_of (@{make_string} (" ^
                    ml_module ^ "." ^
                    mk_free (Proof_Context.init_global thy)
                            Isabelle.argument_main
                            ([]: (string * string) list) ^ "))"
                  , "use \"" ^ SML.Filename.function ml_ext_ml ^ "\""
                  , "ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) (Input.source false (\"let open " ^
                      ml_module ^ " in " ^ Isabelle.function ^ " (\" ^ " ^ arg ^
                      " ^ \") end\") (Position.none, Position.none) )" ]
                  end
             , [ "end" ]]))
         end
    , fn tmp_export_code => fn tmp_file =>
        let open Path
            val stdout_file = Isabelle_System.create_tmp_path "stdout_file" "thy"
            val () = File.write (append tmp_export_code (make [SML.Filename.stdout ml_ext_ml]))
                                (implode (expand stdout_file))
            val (l, (_, exit_st)) =
              compile
                [ "mv " ^ tmp_file ^ " " ^ implode (append tmp_export_code
                                                           (make [SML.Filename.argument ml_ext_ml]))
                , "cd " ^ implode tmp_export_code ^
                  " && echo 'use_thy \"" ^ SML.main ^ "\";' | " ^
                  implode (expand (append (variable "ISABELLE_HOME") (make ["bin", "isabelle"]))) ^
                  " console" ]
                "true"
            val stdout = File.read stdout_file |> (fn s => let val () = File.rm stdout_file in s end)
        in  (l, (stdout, if List.exists (fn (err, _) =>
                              List.exists (fn "*** Error" => true | _ => false)
                                (String.tokens (fn #"\n" => true | _ => false) err)) l then
                           List.app (fn (out, err) => (warning err; writeln out)) l |> K 1
                         else exit_st))
        end)
    end ]
end

structure Find = struct

fun find ml_compiler = 
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME v => v
  | NONE => error ("Not registered compiler: " ^ ml_compiler)

fun ext ml_compiler = case find ml_compiler of (_, ext, _, _, _, _, _) => ext

fun export_mode ml_compiler = case find ml_compiler of (_, _, mode, _, _, _, _) => mode

fun function ml_compiler = case find ml_compiler of (_, _, _, f, _, _, _) => f

fun check_compil ml_compiler = case find ml_compiler of (_, _, _, _, build, _, _) => build

fun init ml_compiler = case find ml_compiler of (_, _, _, _, _, build, _) => build

fun build ml_compiler = case find ml_compiler of (_, _, _, _, _, _, build) => build
end

end
\<close>

ML\<open>
structure Deep = struct

fun absolute_path thy filename =
  Path.implode (Path.append (Resources.master_directory thy) (Path.explode filename))

fun export_code_tmp_file seris g =
  fold
    (fn ((ml_compiler, ml_module), export_arg) => fn f => fn g =>
      f (fn accu =>
        let val tmp_name = Context.theory_name @{theory} in
        (if Deep0.Find.export_mode ml_compiler = Deep0.Export_code_env.Directory then
           Isabelle_System.with_tmp_dir tmp_name
         else
           Isabelle_System.with_tmp_file tmp_name (Deep0.Find.ext ml_compiler))
          (fn filename =>
             g (((((ml_compiler, ml_module), (Path.implode filename, Position.none)), export_arg) :: accu)))
        end))
    seris
    (fn f => f [])
    (g o rev)

fun mk_path_export_code tmp_export_code ml_compiler i =
  Path.append tmp_export_code (Path.make [ml_compiler ^ Int.toString i])

fun export_code_cmd' seris tmp_export_code f_err raw_cs thy =
  export_code_tmp_file seris
    (fn seris =>
      let val mem_scala = List.exists (fn ((("Scala", _), _), _) => true | _ => false) seris
          val _ = Isabelle_Code_Target.export_code_cmd
        false
        (if mem_scala then Deep0.Export_code_env.Isabelle.function :: raw_cs else raw_cs)
        seris
        (Proof_Context.init_global
           let val v = Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.argument thy in
           if mem_scala then Code_printing.apply_code_printing v else v end) in
      List_mapi
        (fn i => fn seri => case seri of (((ml_compiler, _), (filename, _)), _) =>
          let val (l, (out, err)) =
                Deep0.Find.build
                  ml_compiler
                  (mk_path_export_code tmp_export_code ml_compiler i)
                  filename
              val _ = f_err seri err in
          (l, out)
          end) seris
      end)

fun scan thy pos str =
  Symbol.explode str
  |> Source.of_list
  |> Token.source (Thy_Header.get_keywords' thy) pos
  |> Source.exhaust;

fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (scan ctxt Position.none s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

val list_all_eq = fn x0 :: xs =>
  List.all (fn x1 => x0 = x1) xs

end
\<close>

subsection\<open>Saving the History of Meta Commands\<close>

ML\<open>
fun p_gen f g =  f "[" "]" g
              (*|| f "{" "}" g*)
              || f "(" ")" g
fun paren f = p_gen (fn s1 => fn s2 => fn f => Parse.$$$ s1 |-- f --| Parse.$$$ s2) f
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l_with f = Parse.$$$ "[" |-- Scan.optional (Parse.binding --| @{keyword "with_only"} >> SOME) NONE
                     -- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun parse_l1' f = Parse.$$$ "[" |-- Parse.list1 f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
\<close>

ML\<open>
structure Generation_mode = struct

type internal_deep =
  { output_header_thy : (string * (string list (* imports *) * string (* import optional (bootstrap) *))) option
  , seri_args : ((bstring (* compiler *) * bstring (* main module *) ) * Token.T list) list
  , filename_thy : bstring option
  , tmp_export_code : Path.T (* dir *)
  , skip_exportation : bool (* true: skip preview of code exportation *) }

datatype ('a, 'b, 'c) generation_mode0 = Gen_deep of 'a | Gen_shallow of 'b | Gen_syntax_print of 'c

type ('compiler_env_config_ext, 'a) generation_mode =
  { deep : ('compiler_env_config_ext * internal_deep) list
  , shallow : ('compiler_env_config_ext * 'a (* theory init *)) list
  , syntax_print : int option list }

fun mapM_syntax_print f (mode : ('compiler_env_config_ext, 'a) generation_mode) tr = tr
  |> f (#syntax_print mode)
  |> apfst (fn syntax_print => { syntax_print = syntax_print
                               , deep = #deep mode
                               , shallow = #shallow mode })

fun mapM_shallow f (mode : ('compiler_env_config_ext, 'a) generation_mode) tr = tr
  |> f (#shallow mode)
  |> apfst (fn shallow => { syntax_print = #syntax_print mode
                          , deep = #deep mode
                          , shallow = shallow })

fun mapM_deep f (mode : ('compiler_env_config_ext, 'a) generation_mode) tr = tr
  |> f (#deep mode)
  |> apfst (fn deep => { syntax_print = #syntax_print mode
                       , deep = deep
                       , shallow = #shallow mode })

structure Data_gen = Theory_Data
  (type T = (unit META.compiler_env_config_ext, theory) generation_mode
   val empty = {deep = [], shallow = [], syntax_print = [NONE]}
   val extend = I
   fun merge (e1, e2) = { deep = #deep e1 @ #deep e2
                        , shallow = #shallow e1 @ #shallow e2
                        , syntax_print = #syntax_print e1 @ #syntax_print e2 })

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Parse.args --| @{keyword ")"}) []

val parse_scheme =
  @{keyword "design"} >> K META.Gen_only_design || @{keyword "analysis"} >> K META.Gen_only_analysis

val parse_sorry_mode =
  Scan.optional (  @{keyword "SORRY"} >> K (SOME META.Gen_sorry)
                || @{keyword "no_dirty"} >> K (SOME META.Gen_no_dirty)) NONE

val parse_deep =
     Scan.optional (@{keyword "skip_export"} >> K true) false
  -- Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")"
                   -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- parse_l' Parse.name -- Parse.name)
                   --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- parse_sorry_mode
  -- (* code_expr_inP *) parse_l1' (@{keyword "in"} |-- ((@{keyword "self"} || Parse.name)
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional
       ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME)
       NONE

val parse_semantics =
  let val z = 0 in
      Scan.optional
        (paren (@{keyword "generation_semantics"}
               |-- paren (parse_scheme
                          -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat)
                                           z)))
              (META.Gen_default, z)
  end

val mode =
  let fun mk_env output_disable_thy output_header_thy oid_start design_analysis sorry_mode ctxt =
    META.compiler_env_config_empty
    output_disable_thy
    (From.option (From.pair From.string (From.pair (From.list From.string) From.string))
                 output_header_thy)
    (META.oidInit (From.internal_oid oid_start))
    design_analysis
    (sorry_mode, Config.get ctxt quick_and_dirty) in

     @{keyword "deep"} |-- parse_semantics -- parse_deep >>
     (fn ( (design_analysis, oid_start)
         , ( ((((skip_exportation, output_header_thy), output_disable_thy), sorry_mode), seri_args)
           , filename_thy)) =>
         Gen_deep ( mk_env (not output_disable_thy)
                           output_header_thy
                           oid_start
                           design_analysis
                           sorry_mode
                  , { output_header_thy = output_header_thy
                    , seri_args = seri_args
                    , filename_thy = filename_thy
                    , tmp_export_code = Isabelle_System.create_tmp_path "deep_export_code" ""
                    , skip_exportation = skip_exportation }))
  || @{keyword "shallow"} |-- parse_semantics -- parse_sorry_mode >>
     (fn ((design_analysis, oid_start), sorry_mode) =>
       Gen_shallow (mk_env true
                           NONE
                           oid_start
                           design_analysis
                           sorry_mode))
  || (@{keyword "syntax_print"} |-- Scan.optional (Parse.number >> SOME) NONE) >>
     (fn n => Gen_syntax_print (case n of NONE => NONE | SOME n => Int.fromString n))
  end

fun f_command l_mode =
  Toplevel'.setup_theory
    (META.mapM
      (fn Gen_shallow env =>
           pair (fn thy => Gen_shallow (env (Proof_Context.init_global thy), thy))
                o cons (Toplevel'.read_write_keep (Toplevel.Load_previous, Toplevel.Store_backup))
        | Gen_syntax_print n => pair (K (Gen_syntax_print n))
        | Gen_deep (env, i_deep) =>
           pair (fn thy => Gen_deep (env (Proof_Context.init_global thy), i_deep))
                o cons
            (@{command_keyword export_code}, Toplevel'.keep_theory (fn thy =>
              let val seri_args' =
                    List_mapi
                      (fn i => fn ((ml_compiler, ml_module), export_arg) =>
                        let val tmp_export_code = Deep.mk_path_export_code (#tmp_export_code i_deep) ml_compiler i
                            fun mk_fic s = Path.append tmp_export_code (Path.make [s])
                            val () = Deep0.Find.check_compil ml_compiler ()
                            val () = Isabelle_System.mkdirs tmp_export_code in
                        (( ( (ml_compiler, ml_module)
                           , ( Path.implode (if Deep0.Find.export_mode ml_compiler = Deep0.Export_code_env.Directory then
                                               tmp_export_code
                                             else
                                               mk_fic (Deep0.Find.function ml_compiler (Deep0.Find.ext ml_compiler)))
                             , Position.none))
                         , export_arg), mk_fic)
                        end)
                      (List.filter (fn (("self", _), _) => false | _ => true) (#seri_args i_deep))
                  val _ =
                    case seri_args' of [] => () | _ =>
                      let val _ =
                        warning ("After closing Isabelle/jEdit, we may still need to remove this directory (by hand): " ^
                                 Path.implode (Path.expand (#tmp_export_code i_deep))) in
                      thy
                      |> Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.function
                      |> Code_printing.apply_code_printing
                      |> Proof_Context.init_global
                      |>
                      Isabelle_Code_Target.export_code_cmd
                            (List.exists (fn (((("SML", _), _), _), _) => true | _ => false) seri_args')
                            [Deep0.Export_code_env.Isabelle.function]
                            (List.map fst seri_args')
                      end in
                  List.app (fn ((((ml_compiler, ml_module), _), _), mk_fic) =>
                    Deep0.Find.init ml_compiler mk_fic ml_module Deep.mk_free thy) seri_args' end)))
      l_mode
      [])
    (fn l_mode => fn thy =>
      let val l_mode = map (fn f => f thy) l_mode
      in Data_gen.put { deep = map_filter (fn Gen_deep x => SOME x | _ => NONE) l_mode
                      , shallow = map_filter (fn Gen_shallow x => SOME x | _ => NONE) l_mode
                      , syntax_print = map_filter (fn Gen_syntax_print x => SOME x | _ => NONE) l_mode } thy end)

fun update_compiler_config f =
  Data_gen.map
    (fn mode => { deep = map (apfst (META.compiler_env_config_update f)) (#deep mode)
                , shallow = map (apfst (META.compiler_env_config_update f)) (#shallow mode)
                , syntax_print = #syntax_print mode })
end
\<close>

subsection\<open>Factoring All Meta Commands Together\<close>

setup\<open>ML_Antiquotation.inline @{binding mk_string} (Scan.succeed
"(fn ctxt => fn x => ML_Pretty.string_of_polyml (ML_system_pretty (x, FixedInt.fromInt (Config.get ctxt ML_Print_Depth.print_depth))))")
\<close>

ML\<open>

local
  val partition_self = List.partition (fn ((s,_),_) => s = "self")
in

fun exec_deep0 {output_header_thy, seri_args, filename_thy, tmp_export_code, ...} (env, l_obj) =
let open Generation_mode
    val of_arg = META.isabelle_of_compiler_env_config META.isabelle_apply I
    fun def s = Named_Target.theory_map (snd o Specification.definition_cmd NONE [] [] (Binding.empty_atts, s) false)
    val (seri_args0, seri_args) = partition_self seri_args
 in
  fn thy0 =>
  let
    val env = META.compiler_env_config_more_map
                         (fn () => (l_obj, From.option
                                             From.string
                                             (Option.map (Deep.absolute_path thy0) filename_thy)))
                         env
    val l = case seri_args of [] => [] | _ =>
      let val name_main = Deep.mk_free (Proof_Context.init_global thy0)
                                       Deep0.Export_code_env.Isabelle.argument_main []
      in thy0
      |> def (String.concatWith " "
              (  "(" (* polymorphism weakening needed by export_code *)
                  ^ name_main ^ " :: (_ \<times> abr_string option) compiler_env_config_scheme)"
              :: "="
              :: To_string0 (of_arg env)
              :: []))
      |> Deep.export_code_cmd' seri_args
                               tmp_export_code
                               (fn (((_, _), (msg, _)), _) => fn err => if err <> 0 then error msg else ())
                               [name_main]
      end
  in
    case seri_args0 of [] => l
    | _ => ([], case (output_header_thy, filename_thy) of
                  (SOME _, SOME _) => let val _ = META.write_file env in "" end
                | _ => String.concat (map (fn s => s ^ "\n") (snd (META.write_file0 env)))
                       (* TODO: further optimize "string" as "string list" *))
           :: l
  end
  |> (fn l => let val (l_warn, l) = (map fst l, map snd l) in
      if Deep.list_all_eq l then
        (List.concat l_warn, hd l)
      else
        error "There is an extracted language which does not produce a similar Isabelle content as the others"
      end)
  |> (fn (l_warn, s) =>
       let val () = writeln
         (case (output_header_thy, filename_thy) of
            (SOME _, SOME _) => s
          | _ => String.concat (map ( (fn s => s ^ "\n")
                                    o Active.sendback_markup_command
                                    o trim_line)
                                    (String.tokens (fn c => c = META.char_escape) s)))
       in List.app (fn (out, err) => ( writeln (Markup.markup Markup.keyword2 err)
                                     ; case trim_line out of "" => ()
                                       | out => writeln (Markup.markup Markup.keyword1 out)))
                   l_warn end)
end

fun exec_deep i_deep e =
  let val (seri_args0, seri_args) = partition_self (#seri_args i_deep)
  in cons
      ( case (seri_args0, seri_args) of ([_], []) => @{command_keyword print_syntax}
                                      | _ => @{command_keyword export_code}
      , Toplevel'.keep_theory (exec_deep0 i_deep e))
  end
end

local

fun fold_thy_shallow f =
  META.fold_thy_shallow
    (fn f => f () handle ERROR e =>
      ( warning "Shallow Backtracking: (true) Isabelle declarations occurring among the META-simulated ones are ignored (if any)"
        (* TODO automatically determine if there is such Isabelle declarations,
                for raising earlier a specific error message *)
      ; error e))
    f

fun disp_time toplevel_keep_output =
  let
    val tps = Timing.start ()
    val disp_time = fn NONE => I | SOME msg =>
      toplevel_keep_output tps Markup.antiquote
        let val msg = To_string0 msg
        in " " ^ Pretty.string_of
             (Pretty.mark (Name_Space.markup (Proof_Context.const_space @{context}) msg)
                          (Pretty.str msg)) end
  in (tps, disp_time) end

fun thy_deep exec_deep l_obj =
  Generation_mode.mapM_deep
    (META.mapM (fn (env, i_deep) =>
      pair (META.fold_thy_deep l_obj env, i_deep)
           o (if #skip_exportation i_deep then
                I
              else
                exec_deep { output_header_thy = #output_header_thy i_deep
                          , seri_args = #seri_args i_deep
                          , filename_thy = NONE
                          , tmp_export_code = #tmp_export_code i_deep
                          , skip_exportation = #skip_exportation i_deep }
                          ( META.d_output_header_thy_update (K NONE) env, l_obj))))

fun report m f = (Method.report m; f)
fun report_o o' f = (Option.map Method.report o'; f)

fun thy_shallow l_obj get_all_meta_embed =
  Generation_mode.mapM_shallow
    (fn l_shallow => fn thy => META.mapM
      (fn (env, thy0) => fn (thy, l_obj) =>
        let val (_, disp_time) = disp_time (tap o K ooo out_intensify')
            fun aux (env, thy) x =
              fold_thy_shallow
                (K o K thy0)
                (fn msg =>
                  let val () = disp_time msg ()
                      fun in_self f lthy = lthy
                                         |> Local_Theory.new_group
                                         |> f
                                         |> Local_Theory.reset_group
                                         |> Local_Theory.reset
                      fun not_used p _ = error ("not used " ^ Position.here p)
                      val context_of = I
                      fun proof' f = f true
                      fun proofs f s = s |> f |> Seq.the_result ""
                      val proof = I
                      val dual = #seq in
                  fn l => fn (env, thy) =>
                  Bind_META.all_meta_thy { (* specialized part *)
                                           theory = I
                                         , local_theory = K o K Named_Target.theory_map
                                         , local_theory' = K o K (fn f => Named_Target.theory_map (f false))
                                         , keep = fn f => Named_Target.theory_map (fn lthy => (f lthy ; lthy))
                                         , generic_theory = Context.theory_map
                                           (* generic part *)
                                         , context_of = context_of, dual = dual
                                         , proof' = proof', proofs = proofs, proof = proof
                                         , tr_report = report, tr_report_o = report_o
                                         , pr_report = report, pr_report_o = report_o
                                           (* irrelevant part *)
                                         , begin_local_theory = K o not_used @{here}
                                         , local_theory_to_proof' = K o K not_used @{here}
                                         , local_theory_to_proof = K o K not_used @{here}
                                         , tr_raw = not_used @{here} }

                                         { (* specialized part *)
                                           theory = Local_Theory.background_theory
                                         , local_theory = K o K in_self
                                         , local_theory' = K o K (fn f => in_self (f false))
                                         , keep = fn f => in_self (fn lthy => (f lthy ; lthy))
                                         , generic_theory = Context.proof_map
                                           (* generic part *)
                                         , context_of = context_of, dual = dual
                                         , proof' = proof', proofs = proofs, proof = proof
                                         , tr_report = report, tr_report_o = report_o
                                         , pr_report = report, pr_report_o = report_o
                                           (* irrelevant part *)
                                         , begin_local_theory = K o not_used @{here}
                                         , local_theory_to_proof' = K o K not_used @{here}
                                         , local_theory_to_proof = K o K not_used @{here}
                                         , tr_raw = not_used @{here} }

                                         (fn x => fn thy => aux (env, thy) [x])
                                         (pair env)
                                         l
                                         thy
                  end)
                x
                (env, thy)
            val (env, thy) =
              let
                fun disp_time f x =
                let val (s, r) = Timing.timing f x
                    val () = out_intensify (Timing.message s |> Markup.markup Markup.operator) "" in
                  r
                end
              in disp_time (aux (env, thy)) (l_obj ()) end
        in ((env, thy0), (thy, fn _ => get_all_meta_embed (SOME thy))) end)
      l_shallow
      (thy, case l_obj of SOME f => f | NONE => fn _ => get_all_meta_embed (SOME thy))
      |> META.map_prod I fst)

fun thy_switch pos1 pos2 f mode tr =
  ( ( mode
    , Toplevel'.keep
        (fn _ => Output.information ( "Theory required while transitions were being built"
                                    ^ Position.here pos1
                                    ^ ": Commands will not be concurrently considered. "
                                    ^ Markup.markup
                                        (Markup.properties (Position.properties_of pos2) Markup.position)
                                        "(Handled here\092<^here>)")) tr)
  , f #~> Generation_mode.Data_gen.put)

in

fun outer_syntax_commands''' is_safe mk_string cmd_spec cmd_descr parser get_all_meta_embed =
 let open Generation_mode in
  Outer_Syntax.commands' cmd_spec cmd_descr
    (parser >> (fn name => fn thy => fn _ =>
      (* WARNING: Whenever there would be errors raised by functions taking "thy" as input,
                  they will not be shown.
                  So the use of this "thy" can be considered as safe, as long as errors do not happen. *)
      let
        val get_all_m = get_all_meta_embed name
        val m_tr = (Data_gen.get thy, [])
          |-> mapM_syntax_print (META.mapM (fn n =>
                pair n
                     o cons (@{command_keyword print_syntax},
                             Toplevel'.keep_theory (fn thy =>
                               writeln (mk_string
                                         (Proof_Context.init_global
                                           (case n of NONE => thy
                                                    | SOME n => Config.put_global ML_Print_Depth.print_depth n thy))
                                         name)))))
      in let
           val l_obj = get_all_m (is_safe thy)
                       (* In principle, it is fine if (SOME thy) is provided to
                          get_all_m. However, because certain types of errors are most of the
                          time happening whenever certain specific operations depending on thy
                          are explicitly performed, and because get_all_m was intentionally set
                          to not interactively manage such errors, then these errors (whenever
                          they are happening) could possibly not appear in the output
                          window. Although the computation would be in any case interrupted as
                          usual (but with only minimal debugging information, such as a simple
                          red underlining color).
                          
                          Generally, whenever get_all_m is called during the evaluating commands
                          coming from generated files (which is not the case here, but will be
                          later), this restriction can normally be removed (i.e., by writing
                          (SOME thy)), as for the case of generated files, we are taking the
                          assumption that errors (if they are happening) are as hard to detect
                          as if an error was raised somewhere else by the generator itself.
                          Another assumption nevertheless related with the generator is that it
                          is supposed to explicitly not raise errors, however here this
                          get_all_m is not situated below a generating part. This is why we are
                          tempted to mostly give NONE to get_all_m, unless the calling command
                          is explicitly taking the responsibility of a potential failure. *)
           val m_tr = m_tr
                      |-> thy_deep exec_deep l_obj
         in ( m_tr
              |-> mapM_shallow (META.mapM (fn (env, thy_init) => fn acc =>
                    let val (tps, disp_time) = disp_time Toplevel'.keep_output
                        fun aux (env, acc) x =
                          fold_thy_shallow
                            (K (cons (Toplevel'.read_write_keep (Toplevel.Load_backup, Toplevel.Store_default))))
                            (fn msg => fn l => fn (env, acc) => acc
                              |> disp_time msg
                              |> Bind_META.all_meta_tr { context_of = Toplevel.context_of
                                                       , keep = Toplevel.keep
                                                       , generic_theory = Toplevel.generic_theory
                                                       , theory = Toplevel.theory
                                                       , begin_local_theory = Toplevel.begin_local_theory
                                                       , local_theory' = Toplevel.local_theory'
                                                       , local_theory = Toplevel.local_theory
                                                       , local_theory_to_proof' = Toplevel.local_theory_to_proof'
                                                       , local_theory_to_proof = Toplevel.local_theory_to_proof
                                                       , proof' = Toplevel.proof'
                                                       , proofs = Toplevel.proofs
                                                       , proof = Toplevel.proof
                                                         (* *)
                                                       , dual = #par, tr_raw = I
                                                       , tr_report = report, tr_report_o = report_o
                                                       , pr_report = report, pr_report_o = report_o }
                                                       (fn x => fn acc => aux (env, acc) [x])
                                                       (pair env)
                                                       l)
                            x
                            (env, acc)
                    in aux (env, acc) l_obj
                       |> META.map_prod
                            (fn env => (env, thy_init))
                            (Toplevel'.keep_output tps Markup.operator "") end))
            , Data_gen.put)
            handle THY_REQUIRED pos =>
              m_tr |-> thy_switch pos @{here} (thy_shallow NONE get_all_m)
         end
         handle THY_REQUIRED pos =>
           m_tr |-> thy_switch pos @{here} (fn mode => fn thy => 
                                            let val l_obj = get_all_m (SOME thy) in
                                              (thy_deep (tap oo exec_deep0) l_obj
                                                 #~> thy_shallow (SOME (K l_obj)) get_all_m) mode thy
                                            end)
      end
      |> uncurry Toplevel'.setup_theory))
 end
end

fun outer_syntax_commands'' mk_string = outer_syntax_commands''' (K NONE) mk_string

fun outer_syntax_commands' mk_string cmd_spec cmd_descr parser get_all_meta_embed =
  outer_syntax_commands'' mk_string cmd_spec cmd_descr parser (fn a => fn thy => [get_all_meta_embed a thy])

fun outer_syntax_commands'2 mk_string cmd_spec cmd_descr parser get_all_meta_embed =
  outer_syntax_commands''' SOME mk_string cmd_spec cmd_descr parser (fn a => fn thy => [get_all_meta_embed a thy])
\<close>

subsection\<open>Parameterizing the Semantics of Embedded Languages\<close>

ML\<open>
val () = let open Generation_mode in
  Outer_Syntax.commands' @{command_keyword generation_syntax} "set the generating list"
    ((   mode >> (fn x => SOME [x])
      || parse_l' mode >> SOME
      || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => K (K (f_command x))
      | NONE => fn thy => fn _ => []
          |> fold (fn (env, i_deep) => exec_deep i_deep (META.compiler_env_config_reset_all env))
                  (#deep (Data_gen.get thy))
          |> (fn [] => Toplevel'.keep (fn _ => warning "Nothing performed.") []
               | l => l)))
end
\<close>

end
