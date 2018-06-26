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

section\<open>General Environment for the Translation: Conclusion\<close>

theory  Core
imports "core/Floor1_infra"
        "core/Floor1_access"
        "core/Floor1_examp"
        "core/Floor2_examp"
        "core/Floor1_ctxt"
begin

subsection\<open>Preliminaries\<close>

datatype 'a embedding_fun = Embedding_fun_info string 'a
                          | Embedding_fun_simple 'a

datatype ('a, 'b) embedding = Embed_theories "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) embedding_fun list"
                            | Embed_locale "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) embedding_fun list"
                                           "'a \<Rightarrow> 'b \<Rightarrow> semi__locale \<times> 'b"
                                           "('a \<Rightarrow> 'b \<Rightarrow> semi__theory list \<times> 'b) list"

type_synonym 'a embedding' = "('a, compiler_env_config) embedding" (* polymorphism weakening needed by code_reflect *)

definition "L_fold f =
 (\<lambda> Embed_theories l \<Rightarrow> List.fold f l
  | Embed_locale l_th1 loc_data l \<Rightarrow>
      f (Embedding_fun_simple (\<lambda>a b.
          let (loc_data, b) = loc_data a b
            ; (l, b) = List.fold (\<lambda>f0. \<lambda>(l, b) \<Rightarrow> let (x, b) = f0 a b in (x # l, b)) l ([], b) in
          ([META_semi__theories (Theories_locale loc_data (rev l))], b))) o List.fold f l_th1)"

subsection\<open>Preliminaries: Setting Up Aliases Names\<close>

ML\<open>
local
fun definition s = (#2 oo Specification.definition_cmd NONE [] [] (Binding.empty_atts, s)) true
fun def_info lhs rhs = definition (lhs ^ " = " ^
                                     @{const_name Embedding_fun_info} ^
                                       " (\<open>" ^ rhs ^ "\<close>) " ^
                                       rhs)
fun name_print x = String.implode (case String.explode (Long_Name.base_name x) of
      #"p" :: #"r" :: #"i" :: #"n" :: #"t" :: #"_" :: l => l
    | _ => error "'print' expected")
fun name x = "PRINT_" ^ name_print x
fun name1 x = "floor1_PRINT_" ^ name_print x
fun name2 x = "floor2_PRINT_" ^ name_print x
in
fun embedding_fun_info rhs = def_info (name rhs) rhs
fun embedding_fun_simple rhs = definition (name rhs ^ " = " ^
                                            @{const_name Embedding_fun_simple} ^ " (" ^ rhs ^ ")")
fun embedding_fun_info_f1 rhs = def_info (name1 rhs) rhs
fun embedding_fun_simple_f1 rhs = definition (name1 rhs ^ " = " ^
                                            @{const_name Embedding_fun_simple} ^ " (" ^ rhs ^ ")")
fun embedding_fun_info_f2 rhs = def_info (name2 rhs) rhs
fun embedding_fun_simple_f2 rhs = definition (name2 rhs ^ " = " ^
                                            @{const_name Embedding_fun_simple} ^ " (" ^ rhs ^ ")")
fun emb_info rhs = def_info (Long_Name.base_name rhs ^ "\<^sub>i\<^sub>n\<^sub>f\<^sub>o") rhs
fun emb_simple rhs = definition (Long_Name.base_name rhs ^ "\<^sub>s\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>e" ^ " = " ^
                                            @{const_name Embedding_fun_simple} ^ " (" ^ rhs ^ ")")
end
\<close>

(* TODO use antiquotations in cartouches *)
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_type_synonym_class_higher}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_oid_uniq}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_choose}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance_defassoc}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_examp.print_examp_def_st1}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_locale}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st2}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_perm}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_examp.print_transition}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_locale}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_interp}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_ctxt.print_ctxt}\<close>
local_setup \<open>embedding_fun_info @{const_name print_meta_setup_def_state}\<close>
local_setup \<open>embedding_fun_info @{const_name print_meta_setup_def_transition}\<close>

subsection\<open>Assembling Translations\<close>

definition "section_aux n s = start_map' (\<lambda>_. [ O.section (Section n s) ])"
definition "section = section_aux 0"
definition "section' = Embedding_fun_simple o section"
definition "txt f = Embedding_fun_simple (start_map'''' O.text o (\<lambda>_ design_analysis. [Text (f design_analysis)]))"
definition "txt' s = txt (\<lambda>_. s)"
definition "txt'' = txt' o S.flatten"

definition thy_class ::
  (* polymorphism weakening needed by code_reflect *)
  "_ embedding'" where \<open>thy_class =
 (let section = section' o (\<lambda>s. \<open>Class Model: \<close> @@ s) in
  Embed_theories
          [ section \<open>Introduction\<close>
          , txt'' [ \<open>
  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close> ]
          , section \<open>The Construction of the Object Universe\<close>
          , txt'' [ \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close> ]
          , PRINT_infra_datatype_class
          , txt'' [ \<open>
   Now, we construct a concrete ``universe of ToyAny types'' by injection into a
sum type containing the class types. This type of ToyAny will be used as instance
for all respective type-variables. \<close> ]
          , PRINT_infra_datatype_universe
          , txt'' [ \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to Toy types. Again, we exploit that our representation of Toy is a ``shallow embedding'' with a
one-to-one correspondance of Toy-types to types of the meta-language HOL. \<close> ]
          , PRINT_infra_type_synonym_class_higher
          , section \<open>The Accessors\<close>
          , PRINT_access_oid_uniq
          , PRINT_access_choose ])\<close>

definition "thy_enum_flat = Embed_theories []"
definition "thy_enum = Embed_theories []"
definition "thy_class_synonym = Embed_theories []"
definition "thy_class_tree = Embed_theories []"
definition "thy_class_flat = Embed_theories []"
definition "thy_association = Embed_theories []"
definition  thy_instance :: (* polymorphism weakening needed by code_reflect *) "_ embedding'" where
           "thy_instance = Embed_theories
                             [ section' \<open>Instance\<close>
                             , PRINT_examp_instance_defassoc
                             , PRINT_examp_instance ]"
definition "thy_def_base_l = Embed_theories []"
definition "thy_def_state = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                           [ section' \<open>State (Floor 1)\<close>
                                           , floor1_PRINT_examp_def_st1 ]
                             | Floor2 \<Rightarrow> Embed_locale
                                           [ section' \<open>State (Floor 2)\<close> ]
                                           Floor2_examp.print_examp_def_st_locale
                                           [ Floor2_examp.print_examp_def_st2
                                           , Floor2_examp.print_examp_def_st_perm ])"
definition "thy_def_transition = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                              [ section' \<open>Transition (Floor 1)\<close>
                                              , floor1_PRINT_transition ]
                                | Floor2 \<Rightarrow> Embed_locale
                                              [ section' \<open>Transition (Floor 2)\<close> ]
                                              Floor2_examp.print_transition_locale
                                              [ Floor2_examp.print_transition_interp ])"
definition "thy_ctxt = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                      [ section' \<open>Context (Floor 1)\<close>
                                      , floor1_PRINT_ctxt ]
                        | Floor2 \<Rightarrow> Embed_theories
                                      [])"
definition "thy_flush_all = Embed_theories []"
(* NOTE typechecking functions can be put at the end, however checking already defined constants can be done earlier *)

subsection\<open>Combinators Folding the Compiling Environment\<close>

definition "compiler_env_config_reset_all env =
  (let env = compiler_env_config_reset_no_env env in
   ( env \<lparr> D_input_meta := [] \<rparr>
   , let (l_class, l_env) = find_class_ass env in
     L.flatten
       [ l_class
       , List.filter (\<lambda> META_flush_all _ \<Rightarrow> False | _ \<Rightarrow> True) l_env
       , [META_flush_all ToyFlushAll] ] ))"

definition "fold_thy0 meta thy_object0 f =
  L_fold (\<lambda>x (acc1, acc2).
    let (sorry, dirty) = D_output_sorry_dirty acc1
      ; (msg, x) = case x of Embedding_fun_info msg x \<Rightarrow> (Some msg, x)
                           | Embedding_fun_simple x \<Rightarrow> (None, x)
      ; (l, acc1) = x meta acc1 in
    (f msg
       (if sorry = Some Gen_sorry | sorry = None & dirty then
          L.map (map_semi__theory (map_lemma (\<lambda> Lemma n spec _ _ \<Rightarrow> Lemma n spec [] C.sorry
                                                | Lemma_assumes n spec1 spec2 _ _ \<Rightarrow> Lemma_assumes n spec1 spec2 [] C.sorry))) l
        else
          l) acc1 acc2)) thy_object0"

definition "comp_env_input_class_rm f_fold f env_accu =
  (let (env, accu) = f_fold f env_accu in
   (env \<lparr> D_input_class := None \<rparr>, accu))"

definition "comp_env_save ast f_fold f env_accu =
  (let (env, accu) = f_fold f env_accu in
   (env \<lparr> D_input_meta := ast # D_input_meta env \<rparr>, accu))"

definition "comp_env_save_deep ast f_fold =
  comp_env_save ast (\<lambda>f. map_prod
    (case ast of META_def_state Floor1 meta \<Rightarrow> Floor1_examp.print_meta_setup_def_state meta
               | META_def_transition Floor1 meta \<Rightarrow> Floor1_examp.print_meta_setup_def_transition meta
               | _ \<Rightarrow> id)
    id o
    f_fold f)"

definition "comp_env_input_class_mk f_try f_accu_reset f_fold f =
  (\<lambda> (env, accu).
    f_fold f
      (case D_input_class env of Some _ \<Rightarrow> (env, accu) | None \<Rightarrow>
       let (l_class, l_env) = find_class_ass env
         ; (l_enum, l_env) = partition (\<lambda>META_enum _ \<Rightarrow> True | _ \<Rightarrow> False) l_env in
       (f_try (\<lambda> () \<Rightarrow>
         let D_input_meta0 = D_input_meta env
           ; (env, accu) =
               let meta = class_unflat' (arrange_ass True (D_toy_semantics env \<noteq> Gen_default) l_class (L.map (\<lambda> META_enum e \<Rightarrow> e) l_enum))
                 ; (env, accu) = List.fold (\<lambda> ast. comp_env_save ast (case ast of META_enum meta \<Rightarrow> fold_thy0 meta thy_enum) f)
                                           l_enum
                                           (let env = compiler_env_config_reset_no_env env in
                                            (env \<lparr> D_input_meta := List.filter (\<lambda> META_enum _ \<Rightarrow> False | _ \<Rightarrow> True) (D_input_meta env) \<rparr>, f_accu_reset env accu))
                 ; (env, accu) = fold_thy0 meta thy_class f (env, accu) in
               (env \<lparr> D_input_class := Some meta \<rparr>, accu)
           ; (env, accu) =
               List.fold
                 (\<lambda>ast. comp_env_save ast (case ast of
                     META_instance meta \<Rightarrow> fold_thy0 meta thy_instance
                   | META_def_base_l meta \<Rightarrow> fold_thy0 meta thy_def_base_l
                   | META_def_state floor meta \<Rightarrow> fold_thy0 meta (thy_def_state floor)
                   | META_def_transition floor meta \<Rightarrow> fold_thy0 meta (thy_def_transition floor)
                   | META_ctxt floor meta \<Rightarrow> fold_thy0 meta (thy_ctxt floor)
                   | META_flush_all meta \<Rightarrow> fold_thy0 meta thy_flush_all)
                        f)
                 l_env
                 (env \<lparr> D_input_meta := L.flatten [l_class, l_enum] \<rparr>, accu) in
          (env \<lparr> D_input_meta := D_input_meta0 \<rparr>, accu)))))"

definition "comp_env_input_class_bind l f =
  List.fold (\<lambda>x. x f) l"

definition "fold_thy' f_env_save f_try f_accu_reset f =
 (let comp_env_input_class_mk = comp_env_input_class_mk f_try f_accu_reset in
  List.fold (\<lambda> ast.
    f_env_save ast (case ast of
     META_enum meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_enum_flat)
   | META_class_raw Floor1 meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_class_flat)
   | META_association meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_association)
   | META_ass_class Floor1 (ToyAssClass meta_ass meta_class) \<Rightarrow>
       comp_env_input_class_rm (comp_env_input_class_bind [ fold_thy0 meta_ass thy_association
                                                      , fold_thy0 meta_class thy_class_flat ])
   | META_class_synonym meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_class_synonym)
   | META_class_tree meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_class_tree)
   | META_instance meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta thy_instance)
   | META_def_base_l meta \<Rightarrow> fold_thy0 meta thy_def_base_l
   | META_def_state floor meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta (thy_def_state floor))
   | META_def_transition floor meta \<Rightarrow> fold_thy0 meta (thy_def_transition floor)
   | META_ctxt floor meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta (thy_ctxt floor))
   | META_flush_all meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta thy_flush_all)) f))"

definition "compiler_env_config_update f env =
  (* WARNING The semantics of the meta-embedded language is not intended to be reset here (like oid_start), only syntactic configurations of the compiler (path, etc...) *)
 (let env' = f env in
  if D_input_meta env = [] then
    env'
      \<lparr> D_output_disable_thy := D_output_disable_thy env
      , D_output_header_thy := D_output_header_thy env
      (*D_toy_oid_start*)
      (*D_output_position*)
      , D_toy_semantics := D_toy_semantics env
      (*D_input_class*)
      (*D_input_meta*)
      (*D_input_instance*)
      (*D_input_state*)
      (*D_output_header_force*)
      (*D_output_auto_bootstrap*)
      (*D_toy_accessor*)
      (*D_toy_HO_type*)
      , D_output_sorry_dirty := D_output_sorry_dirty env \<rparr>
  else
    fst (fold_thy'
           comp_env_save_deep
           (\<lambda>f. f ())
           (\<lambda>_. id)
           (\<lambda>_ _. Pair)
           (D_input_meta env')
           (env, ())))"

definition "fold_thy_shallow f_try f_accu_reset x =
  fold_thy'
    comp_env_save
    f_try
    f_accu_reset
    (\<lambda>name l acc1.
      map_prod (\<lambda> env. env \<lparr> D_input_meta := D_input_meta acc1 \<rparr>) id
      o List.fold (x name) l
      o Pair acc1)"

definition "fold_thy_deep obj env =
  (case fold_thy'
          comp_env_save_deep
          (\<lambda>f. f ())
          (\<lambda>env _. D_output_position env)
          (\<lambda>_ l acc1 (i, cpt). (acc1, (Succ i, natural_of_nat (List.length l) + cpt)))
          obj
          (env, D_output_position env) of
    (env, output_position) \<Rightarrow> env \<lparr> D_output_position := output_position \<rparr>)"

end
