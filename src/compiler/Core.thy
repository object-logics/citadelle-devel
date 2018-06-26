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
imports "core/Floor1_enum"
        "core/Floor1_infra"
        "core/Floor1_astype"
        "core/Floor1_istypeof"
        "core/Floor1_iskindof"
        "core/Floor1_allinst"
        "core/Floor1_access"
        "core/Floor1_examp"
        "core/Floor2_examp"
        "core/Floor1_ctxt"
        "core/Floor2_ctxt"
        "core/Floor1_haskabelle"
begin

subsection\<open>Preliminaries\<close>

datatype 'a embedding_fun = Embedding_fun_info string 'a
                          | Embedding_fun_simple 'a

datatype ('a, 'b) embedding = Embed_theories "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) embedding_fun list"
                            | Embed_locale "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) embedding_fun list"
                                           "'a \<Rightarrow> 'b \<Rightarrow> semi__locale \<times> 'b"
                                           "('a \<Rightarrow> 'b \<Rightarrow> semi__theory list \<times> 'b) list"
                                           "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) embedding_fun list"

type_synonym 'a embedding' = "('a, compiler_env_config) embedding" (* polymorphism weakening needed by code_reflect *)

definition "L_fold f =
 (let f_locale = \<lambda>loc_data l.
    f (Embedding_fun_simple (\<lambda>a b.
          let (loc_data, b) = loc_data a b
            ; (l, b) = List.fold (\<lambda>f0. \<lambda>(l, b) \<Rightarrow> let (x, b) = f0 a b in (x # l, b)) l ([], b) in
          ([META_semi__theories (Theories_locale loc_data (rev l))], b))) in
  \<lambda> Embed_theories l \<Rightarrow> List.fold f l
  | Embed_locale l_th1 loc_data l_loc l_th2 \<Rightarrow> List.fold f l_th2 o f_locale loc_data l_loc o List.fold f l_th1)"

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
local_setup \<open>embedding_fun_info @{const_name print_infra_enum_synonym}\<close>
local_setup \<open>embedding_fun_info @{const_name print_latex_infra_datatype_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_class_1}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_class_2}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_equiv_2of1}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_equiv_1of2}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_equiv_1_idempo}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_datatype_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_type_synonym_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_type_synonym_class_higher}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_type_synonym_class_rec}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_enum_syn}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_instantiation_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_infra_instantiation_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_instantia_def_strictrefeq}\<close>
local_setup \<open>embedding_fun_info @{const_name print_instantia_lemmas_strictrefeq}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_consts}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_from_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemmas_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemma_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemmas_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemma_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemmas_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_defined}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_up_d_cast0}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_up_d_cast}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_d_up_cast}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemma_const}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemmas_const}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_consts}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_from_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_lemmas_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_lemma_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_lemmas_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_lemma_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_lemmas_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_defined}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_defined'}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_up_larger}\<close>
local_setup \<open>embedding_fun_info @{const_name print_istypeof_up_d_cast}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_consts}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_class}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_from_universe}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_lemmas_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_lemma_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_lemmas_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_lemma_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_lemmas_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_defined}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_defined'}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_up_eq_asty}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_up_larger}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_up_istypeof_unfold}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_up_istypeof}\<close>
local_setup \<open>embedding_fun_info @{const_name print_iskindof_up_d_cast}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_def_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_lemmas_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_astype}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_exec}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_istypeof_pre}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_istypeof}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_iskindof_eq}\<close>
local_setup \<open>embedding_fun_info @{const_name print_allinst_iskindof_larger}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_oid_uniq_ml}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_oid_uniq}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_eval_extract}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_choose_ml}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_choose}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_deref_oid}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_deref_assocs}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_select}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_select_obj}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot_consts}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot_lemmas_id}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot_cp_lemmas}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot_lemma_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_dot_lemmas_cp}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_lemma_strict}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_def_mono}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_is_repr}\<close>
local_setup \<open>embedding_fun_info @{const_name print_access_repr_allinst}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_def_st_defs}\<close>
local_setup \<open>embedding_fun_info @{const_name print_astype_lemmas_id2}\<close>
local_setup \<open>embedding_fun_info @{const_name print_enum}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance_defassoc_typecheck_var}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance_defassoc}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_instance_defassoc_typecheck}\<close>
local_setup \<open>embedding_fun_info @{const_name print_examp_oclbase}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_examp.print_examp_def_st_typecheck_var}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_examp.print_examp_def_st1}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_locale}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st2}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_dom}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_dom_lemmas}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_perm}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_allinst}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_defassoc_typecheck}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_examp_def_st_def_interp}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_examp.print_transition}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_locale}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_interp}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_def_state}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_wff}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_where}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_def_interp}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_examp.print_transition_lemmas_oid}\<close>
local_setup \<open>embedding_fun_info_f1 @{const_name Floor1_ctxt.print_ctxt}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_ctxt.print_ctxt_pre_post}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_ctxt.print_ctxt_inv}\<close>
local_setup \<open>embedding_fun_info_f2 @{const_name Floor2_ctxt.print_ctxt_thm}\<close>
local_setup \<open>embedding_fun_info @{const_name print_meta_setup_def_state}\<close>
local_setup \<open>embedding_fun_info @{const_name print_meta_setup_def_transition}\<close>
local_setup \<open>embedding_fun_info @{const_name print_haskell}\<close>

subsection\<open>Assembling Translations\<close>

definition "section_aux n s = start_map' (\<lambda>_. [ O.section (Section n s) ])"
definition "section = section_aux 0"
definition "subsection = section_aux 1"
definition "subsubsection = section_aux 2"
definition "section' = Embedding_fun_simple o section"
definition "subsection' = Embedding_fun_simple o subsection"
definition "txt f = Embedding_fun_simple (start_map'''''' O.text o (\<lambda>_ n_thy design_analysis. [Text (f n_thy design_analysis)]))"
definition "txt_raw f = Embedding_fun_simple (start_map'''''' O.text_raw o (\<lambda>_ n_thy design_analysis. [Text_raw (f n_thy design_analysis)]))"
definition "txt' s = txt (\<lambda>_ _. s)"
definition "txt'' = txt' o S.flatten"
definition "txt''d s = txt (\<lambda> _. \<lambda> Gen_only_design \<Rightarrow> S.flatten (s) | _ \<Rightarrow> \<open>\<close>)"
definition "txt''d' s = txt (\<lambda> n_thy. \<lambda> Gen_only_design \<Rightarrow> S.flatten (s n_thy) | _ \<Rightarrow> \<open>\<close>)"
definition "txt_raw''d' s = txt_raw (\<lambda> n_thy. \<lambda> Gen_only_design \<Rightarrow> S.flatten (s n_thy) | _ \<Rightarrow> \<open>\<close>)"
definition "txt''a s = txt (\<lambda> _. \<lambda> Gen_only_design \<Rightarrow> \<open>\<close> | _ \<Rightarrow> S.flatten s)"
definition "txt''a' s = txt (\<lambda> n_thy. \<lambda> Gen_only_design \<Rightarrow> \<open>\<close> | _ \<Rightarrow> S.flatten (s n_thy))"
definition "txt_raw''a' s = txt_raw (\<lambda> n_thy. \<lambda> Gen_only_design \<Rightarrow> \<open>\<close> | _ \<Rightarrow> S.flatten (s n_thy))"

definition thy_class ::
  (* polymorphism weakening needed by code_reflect *)
  "_ embedding'" where \<open>thy_class =
  (let section = section' o (\<lambda>s. \<open>Class Model: \<close> @@ s)
     ; subsection = subsection'
     ; subsection_def = subsection \<open>Definition\<close>
     ; subsection_cp = subsection \<open>Context Passing\<close>
     ; subsection_exec = subsection \<open>Execution with Invalid or Null as Argument\<close>
     ; subsection_defined = subsection \<open>Validity and Definedness Properties\<close>
     ; subsection_up = subsection \<open>Up Down Casting\<close>
     ; subsection_const = subsection \<open>Const\<close> in
  (Embed_theories o L.flatten)
          [ [ PRINT_infra_enum_synonym ]
          , [ txt''d' (\<lambda>n_thy. [ \<open>
   \label{ex:\<close> @@ n_thy \<open>employee-design:uml\<close> @@ \<open>} \<close> ])
            , txt''a' (\<lambda>n_thy. [ \<open>
   \label{ex:\<close> @@ n_thy \<open>employee-analysis:uml\<close> @@ \<open>} \<close> ])
            , section \<open>Introduction\<close>
            , txt'' [ \<open>

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside \HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close> ]
            , txt'' [ \<open>
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the \ML level.  This has been done, for a semantics
  following the open-world assumption, for \UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for \UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/\HOL. \<close> ]
            , subsection \<open>Outlining the Example\<close>
            , txt''d' (\<lambda>n_thy. [ \<open>
   We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the \OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the \UML class model (see \autoref{fig:\<close> @@ n_thy \<open>person\<close> @@ \<open>}):\<close> ])
            , txt''a' (\<lambda>n_thy. [ \<open>
   We are presenting here an ``analysis-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the \OCL standard~\cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model''.
To be precise, this theory contains the formalization of the data-part
covered by the \UML class model (see \autoref{fig:\<close> @@ n_thy \<open>person-ana\<close> @@ \<open>}):\<close>
(* (see \autoref{ex:employee-design:uml})*) ])
            , txt_raw''d' (\<lambda> n_thy. [ \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple \UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:\<close> @@ n_thy \<open>person\<close> @@ \<open>}}
\end{figure}
\<close> ])
            , txt_raw''a' (\<lambda> n_thy. [ \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple \UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:\<close> @@ n_thy \<open>person-ana\<close> @@ \<open>}}
\end{figure}
\<close> ])
            , txt'' [ \<open>
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the \OCL part
captured by the subsequent theory).
\<close> ]
            , section \<open>The Construction of the Object Universe\<close>
            (*, txt'' [ \<open>
   Ideally, the following is generated automatically from a \UML class model.  \<close> ]
            *), txt'' [ \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close> ]
            (*, PRINT_latex_infra_datatype_class*)
            , PRINT_infra_datatype_class_1
            , PRINT_infra_datatype_class_2
            , PRINT_infra_datatype_equiv_2of1
            , PRINT_infra_datatype_equiv_1of2
            (*, PRINT_infra_datatype_equiv_1_idempo*)
            , txt'' [ \<open>
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. \<close> ]
            , PRINT_infra_datatype_universe
            , txt'' [ \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to \OCL types. Again, we exploit that our representation of \OCL is a ``shallow embedding'' with a
one-to-one correspondance of \OCL-types to types of the meta-language \HOL. \<close> ]
            , PRINT_infra_type_synonym_class
            , PRINT_infra_type_synonym_class_higher
            , PRINT_infra_type_synonym_class_rec
            , PRINT_infra_enum_syn
            (*, txt'' [ \<open>
   Just a little check: \<close> ]
            *), txt'' [ \<open>
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the Object ID (oid) of the object. \<close> ]
            , PRINT_infra_instantiation_class
            , PRINT_infra_instantiation_universe

            , section \<open>Instantiation of the Generic Strict Equality\<close>
            , txt'' [ \<open>
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"} \<close> ]
            , PRINT_instantia_def_strictrefeq
            , PRINT_instantia_lemmas_strictrefeq
            , txt'' [ \<open>
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close> ]
            , txt'' [ \<open>
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close> ] ]

          , L.flatten (L.map (\<lambda>(title, body_def, body_cp, body_exec, body_defined, body_up, body_const).
              section title # L.flatten [ subsection_def # body_def
                                      , subsection_cp # body_cp
                                      , subsection_exec # body_exec
                                      , subsection_defined # body_defined
                                      , subsection_up # body_up
                                      , subsection_const # body_const ])
          [ (\<open>OclAsType\<close>,
            [ PRINT_astype_consts
            , PRINT_astype_class
            , PRINT_astype_from_universe
            , PRINT_astype_lemmas_id ]
            , [ PRINT_astype_lemma_cp
            , PRINT_astype_lemmas_cp ]
            , [ PRINT_astype_lemma_strict
            , PRINT_astype_lemmas_strict ]
            , [ PRINT_astype_defined ]
            , [ PRINT_astype_up_d_cast0
            , PRINT_astype_up_d_cast
            , PRINT_astype_d_up_cast ]
            , [ PRINT_astype_lemma_const
              , PRINT_astype_lemmas_const ])

          , (\<open>OclIsTypeOf\<close>,
            [ PRINT_istypeof_consts
            , PRINT_istypeof_class
            , PRINT_istypeof_from_universe
            , PRINT_istypeof_lemmas_id ]
            , [ PRINT_istypeof_lemma_cp
            , PRINT_istypeof_lemmas_cp ]
            , [ PRINT_istypeof_lemma_strict
            , PRINT_istypeof_lemmas_strict ]
            , [ PRINT_istypeof_defined
            , PRINT_istypeof_defined' ]
            , [ PRINT_istypeof_up_larger
            , PRINT_istypeof_up_d_cast ]
            , [])

          , (\<open>OclIsKindOf\<close>,
            [ PRINT_iskindof_consts
            , PRINT_iskindof_class
            , PRINT_iskindof_from_universe
            , PRINT_iskindof_lemmas_id ]
            , [ PRINT_iskindof_lemma_cp
            , PRINT_iskindof_lemmas_cp ]
            , [ PRINT_iskindof_lemma_strict
            , PRINT_iskindof_lemmas_strict ]
            , [ PRINT_iskindof_defined
            , PRINT_iskindof_defined' ]
            , [ PRINT_iskindof_up_eq_asty
            , PRINT_iskindof_up_larger
            , PRINT_iskindof_up_istypeof_unfold
            , PRINT_iskindof_up_istypeof
            , PRINT_iskindof_up_d_cast ]
            , []) ])

          , [ section \<open>OclAllInstances\<close>
            , txt'' [ \<open>
   To denote \OCL-types occurring in \OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.'' \<close> ]
            , PRINT_allinst_def_id
            , PRINT_allinst_lemmas_id
            , PRINT_allinst_astype
            , PRINT_allinst_exec
            , subsection \<open>OclIsTypeOf\<close>
            , PRINT_allinst_istypeof_pre
            , PRINT_allinst_istypeof
            , subsection \<open>OclIsKindOf\<close>
            , PRINT_allinst_iskindof_eq
            , PRINT_allinst_iskindof_larger

            , section \<open>The Accessors\<close>
            , txt''d' (\<lambda>n_thy. [ \<open>
  \label{sec:\<close> @@ n_thy \<open>edm-accessors\<close> @@ \<open>}\<close> ])
            , txt''a' (\<lambda>n_thy. [ \<open>
  \label{sec:\<close> @@ n_thy \<open>eam-accessors\<close> @@ \<open>}\<close> ])
            (*, txt'' [ \<open>
   Should be generated entirely from a class-diagram. \<close> ]
            *), subsection_def
            , txt''a [ \<open>
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.'' \<close> ]
            , PRINT_access_oid_uniq_ml
            , PRINT_access_oid_uniq
            , txt''a [ \<open>
   From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).\<close> ]
            , PRINT_access_eval_extract
            , txt''a [ \<open>
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}: \<close> ]
            , PRINT_access_choose_ml
            , PRINT_access_choose
            , PRINT_access_deref_oid
            , PRINT_access_deref_assocs
            , txt'' [ \<open>
   pointer undefined in state or not referencing a type conform object representation \<close> ]
            , PRINT_access_select
            , PRINT_access_select_obj
            , PRINT_access_dot_consts
            , PRINT_access_dot
            , PRINT_access_dot_lemmas_id
            , subsection_cp
            , PRINT_access_dot_cp_lemmas
            , PRINT_access_dot_lemma_cp
            , PRINT_access_dot_lemmas_cp
            , subsection_exec
            , PRINT_access_lemma_strict
            , subsection \<open>Representation in States\<close>
            , PRINT_access_def_mono
            , PRINT_access_is_repr
            , PRINT_access_repr_allinst

            , section \<open>Towards the Object Instances\<close>
            , txt''d' (\<lambda>n_thy. [ \<open>

The example we are defining in this section comes from the \autoref{fig:\<close> @@ n_thy \<open>edm1_system-states\<close> @@ \<open>}.
\<close> ])
            , txt_raw''d' (\<lambda>n_thy. [ \<open>
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:\<close> @@ n_thy \<open>edm1_system-states\<close> @@ \<open>}
\end{figure}
\<close> ])
            , txt''a' (\<lambda>n_thy. [ \<open>

The example we are defining in this section comes from the \autoref{fig:\<close> @@ n_thy \<open>eam1_system-states\<close> @@ \<open>}.
\<close> ])
            , txt_raw''a' (\<lambda>n_thy. [ \<open>
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:\<close> @@ n_thy \<open>eam1_system-states\<close> @@ \<open>}
\end{figure}
\<close> ])
            , PRINT_examp_def_st_defs
            , PRINT_astype_lemmas_id2 ] ])\<close>

definition "thy_enum_flat = Embed_theories []"
definition  thy_enum :: (* polymorphism weakening needed by code_reflect *) "_ embedding'" where
           "thy_enum = Embed_theories [ section' \<open>Enum\<close>
                                      , PRINT_enum ]"
definition  thy_haskell :: (* polymorphism weakening needed by code_reflect *) "_ embedding'" where
           "thy_haskell = Embed_theories [ section' \<open>Haskell\<close>
                                         , PRINT_haskell ]"
definition "thy_class_synonym = Embed_theories []"
definition "thy_class_tree = Embed_theories []"
definition "thy_class_flat = Embed_theories []"
definition "thy_association = Embed_theories []"
definition  thy_instance :: (* polymorphism weakening needed by code_reflect *) "_ embedding'" where
           "thy_instance = Embed_theories
                             [ section' \<open>Instance\<close>
                             , PRINT_examp_instance_defassoc_typecheck_var
                             , PRINT_examp_instance_defassoc
                             , PRINT_examp_instance
                             , PRINT_examp_instance_defassoc_typecheck ]"
definition  thy_def_base_l :: (* polymorphism weakening needed by code_reflect *) "_ embedding'" where
           "thy_def_base_l = Embed_theories [ section' \<open>BaseType\<close>
                                            , PRINT_examp_oclbase ]"
definition "thy_def_state = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                           [ section' \<open>State (Floor 1)\<close>
                                           , floor1_PRINT_examp_def_st_typecheck_var
                                           , floor1_PRINT_examp_def_st1 ]
                             | Floor2 \<Rightarrow> Embed_locale
                                           [ section' \<open>State (Floor 2)\<close> ]
                                           Floor2_examp.print_examp_def_st_locale
                                           [ Floor2_examp.print_examp_def_st2
                                           , Floor2_examp.print_examp_def_st_dom
                                           , Floor2_examp.print_examp_def_st_dom_lemmas
                                           , Floor2_examp.print_examp_def_st_perm
                                           , Floor2_examp.print_examp_def_st_allinst
                                           , Floor2_examp.print_examp_def_st_defassoc_typecheck ]
                                           [ floor2_PRINT_examp_def_st_def_interp ])"
definition "thy_def_transition = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                              [ section' \<open>Transition (Floor 1)\<close>
                                              , floor1_PRINT_transition ]
                                | Floor2 \<Rightarrow> Embed_locale
                                              [ section' \<open>Transition (Floor 2)\<close> ]
                                              Floor2_examp.print_transition_locale
                                              [ Floor2_examp.print_transition_interp
                                              , Floor2_examp.print_transition_def_state
                                              , Floor2_examp.print_transition_wff
                                              , Floor2_examp.print_transition_where ]
                                              [ floor2_PRINT_transition_def_interp
                                              , floor2_PRINT_transition_lemmas_oid ])"
definition "thy_ctxt = (\<lambda> Floor1 \<Rightarrow> Embed_theories
                                      [ section' \<open>Context (Floor 1)\<close>
                                      , floor1_PRINT_ctxt ]
                        | Floor2 \<Rightarrow> Embed_theories
                                      [ section' \<open>Context (Floor 2)\<close>
                                      , floor2_PRINT_ctxt_pre_post
                                      , floor2_PRINT_ctxt_inv
                                      , floor2_PRINT_ctxt_thm ])"
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
       , [META_flush_all OclFlushAll] ] ))"

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
               let meta = class_unflat' (arrange_ass True (D_ocl_semantics env \<noteq> Gen_default) l_class (L.map (\<lambda> META_enum e \<Rightarrow> e) l_enum))
                 ; (env, accu) = List.fold (\<lambda> ast. comp_env_save ast (case ast of META_enum meta \<Rightarrow> fold_thy0 meta thy_enum) f)
                                           l_enum
                                           (let env = compiler_env_config_reset_no_env env in
                                            (env \<lparr> D_input_meta := List.filter (\<lambda> META_enum _ \<Rightarrow> False | _ \<Rightarrow> True) (D_input_meta env) \<rparr>, f_accu_reset env accu))
                 ; (env, accu) = fold_thy0 meta thy_class f (env, accu) in
               (env \<lparr> D_input_class := Some meta \<rparr>, accu)
           ; (env, accu) =
               List.fold
                 (\<lambda>ast. comp_env_save ast (case ast of
                     META_haskell meta \<Rightarrow> fold_thy0 meta thy_haskell
                   | META_instance meta \<Rightarrow> fold_thy0 meta thy_instance
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
   | META_ass_class Floor1 (OclAssClass meta_ass meta_class) \<Rightarrow>
       comp_env_input_class_rm (comp_env_input_class_bind [ fold_thy0 meta_ass thy_association
                                                      , fold_thy0 meta_class thy_class_flat ])
   | META_haskell meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta thy_haskell)
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
      (*D_ocl_oid_start*)
      (*D_output_position*)
      , D_ocl_semantics := D_ocl_semantics env
      (*D_input_class*)
      (*D_input_meta*)
      (*D_input_instance*)
      (*D_input_state*)
      (*D_output_header_force*)
      (*D_output_auto_bootstrap*)
      (*D_ocl_accessor*)
      (*D_ocl_HO_type*)
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
