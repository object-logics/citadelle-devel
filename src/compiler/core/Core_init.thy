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

chapter\<open>Translating Meta-Models\<close>
section\<open>General Environment for the Translation: Introduction\<close>

theory  Core_init
imports "../Static"
        "../meta/Meta_META"
begin

text\<open>This file regroups common utilities used by the embedding functions of OCL in Isabelle.\<close>

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply standard
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply (simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_internal_oid_def)
end

instantiation opt_ident :: linorder
begin
 definition "n_of_opt_ident = (\<lambda> OptIdent n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_opt_ident n \<le> n_of_opt_ident m"
 definition "n < m \<longleftrightarrow> n_of_opt_ident n < n_of_opt_ident m"
 instance
 apply standard
 apply (metis less_eq_opt_ident_def less_imp_le less_opt_ident_def not_less)
 apply (metis less_eq_opt_ident_def order_refl)
   apply (metis less_eq_opt_ident_def order.trans)
   apply (simp add: less_eq_opt_ident_def n_of_opt_ident_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_opt_ident_def)
end


definition "const_oclastype = \<open>OclAsType\<close>"
definition "const_oclistypeof = \<open>OclIsTypeOf\<close>"
definition "const_ocliskindof = \<open>OclIsKindOf\<close>"
definition "const_mixfix dot_ocl name = S.flatten [dot_ocl, \<open>'(\<close>, name, \<open>')\<close>]"
definition "const_oid_of s = \<open>oid_of_\<close> @@ s"
definition "dot_oclastype = \<open>.oclAsType\<close>"
definition "dot_oclistypeof = \<open>.oclIsTypeOf\<close>"
definition "dot_ocliskindof = \<open>.oclIsKindOf\<close>"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_reconst_basetype = \<open>reconst_basetype\<close>"
definition "var_reconst_basetype_void = \<open>reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d\<close>"
definition "var_Abs_Void = \<open>Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_oid_uniq = \<open>oid\<close>"
definition "var_eval_extract = \<open>eval_extract\<close>"
definition "var_deref = \<open>deref\<close>"
definition "var_deref_oid = \<open>deref_oid\<close>"
definition "var_deref_assocs = \<open>deref_assocs\<close>"
definition "var_deref_assocs_list = \<open>deref_assocs_list\<close>"
definition "var_inst_assoc = \<open>inst_assoc\<close>"
definition "var_select = \<open>select\<close>"
definition "var_select_object = \<open>select_object\<close>"
definition "var_select_object_set = \<open>select_object\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_set_any = \<open>select_object_any\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_set_any_exec = \<open>select_object_any_exec\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_sequence = \<open>select_object\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_sequence_any = \<open>select_object_any\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_sequence_any_exec = \<open>select_object_any_exec\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_pair = \<open>select_object\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_select_object_pair_any = \<open>select_object_any\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_select_object_pair_any_exec = \<open>select_object_any_exec\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_choose = \<open>choose\<close>"
definition "var_switch = \<open>switch\<close>"
definition "var_assocs = \<open>assocs\<close>"
definition "var_map_of_list = \<open>map_of_list\<close>"
definition "var_OclInteger = \<open>OclInt\<close>"
definition "var_OclReal = \<open>OclReal\<close>"
definition "var_OclString = \<open>OclString\<close>"
definition "var_Abs_Set = \<open>Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Abs_Set_inverse = var_Abs_Set @@ \<open>_inverse\<close>"
definition "var_Set_base = \<open>Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Sequence_base = \<open>Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Pair_base = \<open>Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_mt_set = \<open>mtSet\<close>"
definition "var_ANY_set = \<open>UML_Set.OclANY\<close>"
definition "var_OclIncluding_set = \<open>UML_Set.OclIncluding\<close>"
definition "var_OclForall_set = \<open>UML_Set.OclForall\<close>"
definition "var_mt_sequence = \<open>mtSequence\<close>"
definition "var_ANY_sequence = \<open>UML_Sequence.OclANY\<close>"
definition "var_OclIncluding_sequence = \<open>UML_Sequence.OclIncluding\<close>"
definition "var_OclForall_sequence = \<open>UML_Sequence.OclForall\<close>"
definition "var_self = \<open>self\<close>"
definition "var_result = \<open>result\<close>"
definition "var_val' = \<open>val'\<close>"
definition "update_D_ocl_accessor_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_ocl_accessor_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

definition "Term_basety = (let var_x = \<open>x\<close> in
                           Term_lambdas [var_x, wildcard] (Term_some (Term_some (Term_basic [var_x]))))"

datatype 'a tree = Tree 'a "'a tree list"

fun make_tree
and make_tree' where
   "make_tree l_pos nb_child deep =
      Tree l_pos (case deep of 0 \<Rightarrow> []
                  | Suc deep \<Rightarrow> make_tree' l_pos nb_child nb_child deep [])"

 | "make_tree' l_pos nb_child i deep l =
     (case i of 0 \<Rightarrow> l
      | Suc i \<Rightarrow> make_tree' l_pos nb_child i deep (make_tree (i # l_pos) nb_child deep # l))"

definition "ident_fresh = (\<lambda>l (map, ident).
  case RBT.lookup map l of None \<Rightarrow> (ident, (RBT.insert l ident map, Suc ident))
  | Some i \<Rightarrow> (i, (map, ident)))"

definition "ident_empty = (RBT.empty, 0)"

definition "ident_current = snd"

fun fold_tree where
   "fold_tree f t accu =
     (case t of Tree _ [] \<Rightarrow> accu
      | Tree x l \<Rightarrow>
          List.fold
            (fold_tree f)
            l
            (List.fold
              (\<lambda>t accu. case t of Tree x' _ \<Rightarrow> f x x' accu)
              l
              accu))"

datatype 'a class_output = C_out_OclAny | C_out_simple 'a

definition "mk_tree nb_child deep n_init =
 (let (l, map) =
    fold_tree
      (\<lambda> l1 l2 (l, map).
          let (n1, map) = ident_fresh l1 map
          ; (n2, map) = ident_fresh l2 map in
          ((if n1 = 0 then
              C_out_OclAny
            else
              C_out_simple (String.nat_to_digit26 (n1 + n_init)), String.nat_to_digit26 (n2 + n_init)) # l, map))
      (make_tree [] nb_child deep)
      ([], ident_empty) in
  (rev l, n_init + ident_current map - 1))"

definition "find_class_ass env =
 (let (l_tree, l_all_meta) =
    partition (\<lambda> META_class_tree _ \<Rightarrow> True
               | _ \<Rightarrow> False) (rev (D_input_meta env))
  ; (l_class, l_all_meta) =
    partition (let f = \<lambda>class. ClassRaw_clause class = [] in
               \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
               | META_association _ \<Rightarrow> True
               | META_ass_class Floor1 (OclAssClass _ class) \<Rightarrow> f class
               | META_class_synonym _ \<Rightarrow> True
               | _ \<Rightarrow> False) (l_all_meta) in
  ( L.flatten [ (* generate a set of 'Class' from 'Tree _ _' *)
                L.map (let mk = \<lambda>n1 n2.
                         META_class_raw Floor1 (ocl_class_raw.make
                           (OclTyObj (OclTyCore_pre n1)
                                     (case n2 of None \<Rightarrow> []
                                               | Some n2 \<Rightarrow> [[OclTyCore_pre n2]]))
                           []
                           []
                           False) in
                       \<lambda> (C_out_OclAny, s) \<Rightarrow> mk s None
                       | (C_out_simple s1, s2) \<Rightarrow> mk s2 (Some s1))
                      (concat (fst (L.mapM (\<lambda> META_class_tree (OclClassTree n1 n2) \<Rightarrow>
                                                mk_tree (nat_of_natural n1) (nat_of_natural n2))
                                           l_tree
                                           0)))
              , l_class
              , List.map_filter (let f = \<lambda>class. class \<lparr> ClassRaw_clause := [] \<rparr> in
                                 \<lambda> META_class_raw Floor1 c \<Rightarrow> Some (META_class_raw Floor1 (f c))
                                 | META_ass_class Floor1 (OclAssClass ass class) \<Rightarrow> Some (META_ass_class Floor1 (OclAssClass ass (f class)))
                                 | _ \<Rightarrow> None) l_all_meta ]
  , L.flatten (L.map
      (let f = \<lambda>class. [ META_ctxt Floor1 (ocl_ctxt_ext [] (ClassRaw_name class) (ClassRaw_clause class) ()) ] in
       \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
       | META_ass_class Floor1 (OclAssClass _ class) \<Rightarrow> f class
       | x \<Rightarrow> [x]) l_all_meta)))"

definition "map_enum_syn l_enum l_syn =
 (\<lambda> OclTy_object (OclTyObj (OclTyCore_pre s) []) \<Rightarrow>
      if list_ex (\<lambda>syn. s \<triangleq> (case syn of OclClassSynonym n _ \<Rightarrow> n)) l_syn then
        OclTy_class_syn s
      else if list_ex (\<lambda>enum. s \<triangleq> (case enum of OclEnum n _ \<Rightarrow> n)) l_enum then
        OclTy_enum s
      else
        OclTy_object (OclTyObj (OclTyCore_pre s) [])
  | x \<Rightarrow> x)"

definition "arrange_ass with_aggreg with_optim_ass l_c l_enum =
   (let l_syn = List.map_filter (\<lambda> META_class_synonym e \<Rightarrow> Some e
                                 | _ \<Rightarrow> None) l_c
      ; l_class = List.map_filter (\<lambda> META_class_raw Floor1 cflat \<Rightarrow> Some cflat
                                   | META_ass_class Floor1 (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                   | _ \<Rightarrow> None) l_c
      ; l_class = (* map classes: change the (enumeration) type of every attributes to 'raw'
                                instead of the default 'object' type *)
        L.map
          (\<lambda> cflat \<Rightarrow>
            cflat \<lparr> ClassRaw_own :=
                      L.map (map_prod id (map_enum_syn l_enum l_syn))
                               (ClassRaw_own cflat) \<rparr>) l_class
    ; l_ass = List.map_filter (\<lambda> META_association ass \<Rightarrow> Some ass
                                 | META_ass_class Floor1 (OclAssClass ass _) \<Rightarrow> Some ass
                                 | _ \<Rightarrow> None) l_c
      ; OclMult = \<lambda>l set. ocl_multiplicity_ext l None set ()
      ; (l_class, l_ass0) =
          if with_optim_ass then
            (* move from classes to associations:
                 attributes of object types
                 + those constructed with at most 1 recursive call to OclTy_collection *)
            map_prod rev rev (List.fold
                  (\<lambda>c (l_class, l_ass).
                    let default = [Set]
                      ; f = \<lambda>role t mult_out. \<lparr> OclAss_type = OclAssTy_native_attribute
                                              , OclAss_relation = OclAssRel [(ClassRaw_name c, OclMult [(Mult_star, None)] default)
                                                                            ,(t, mult_out \<lparr> TyRole := Some role \<rparr>)] \<rparr>
                      ; (l_own, l_ass) =
                        List.fold (\<lambda> (role, OclTy_object t) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t (OclMult [(Mult_nat 0, Some (Mult_nat 1))] default) # l)
                                   | (role, OclTy_collection mult (OclTy_object t)) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t mult # l)
                                   | x \<Rightarrow> \<lambda> (l_own, l). (x # l_own, l))
                                  (ClassRaw_own c)
                                  ([], l_ass) in
                    (c \<lparr> ClassRaw_own := rev l_own \<rparr> # l_class, l_ass))
                  l_class
                  ([], []))
          else
            (l_class, [])
      ; (l_class, l_ass) =
          if with_aggreg then
            (* move from associations to classes:
                 attributes of aggregation form *)
            map_prod rev rev (List.fold
            (\<lambda>ass (l_class, l_ass).
              if OclAss_type ass = OclAssTy_aggregation then
                ( fold_max
                    (\<lambda> (cpt_to, (name_to, category_to)).
                      case TyRole category_to of
                        Some role_to \<Rightarrow>
                        List.fold (\<lambda> (cpt_from, (name_from, multip_from)).
                          L.map_find (\<lambda>cflat.
                            if cl_name_to_string cflat \<triangleq> ty_obj_to_string name_from then
                              Some (cflat \<lparr> ClassRaw_own :=
                                              L.flatten [ ClassRaw_own cflat
                                                           , [(role_to, let ty = OclTy_object name_to in
                                                                        if single_multip category_to then
                                                                          ty
                                                                        else
                                                                          OclTy_collection category_to ty)]] \<rparr>)
                            else None))
                     | _ \<Rightarrow> \<lambda>_. id)
                    (OclAss_relation' ass)
                    l_class
                , l_ass)
              else
                (l_class, ass # l_ass)) l_ass (l_class, []))
          else
            (l_class, l_ass) in
    ( l_class
    , L.flatten [l_ass, l_ass0]))"

definition "datatype_name = \<open>ty\<close>"
definition "datatype_ext_name = datatype_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype_constr_name = \<open>mk\<close>"
definition "datatype_ext_constr_name = datatype_constr_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype'_ext_name = \<open>ty2\<close>"
definition "datatype'_ext'_name = datatype'_ext_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype'_name = datatype'_ext_name @@ const_oid"
definition "datatype'_ext_constr_name = \<open>mk2\<close>"
definition "datatype'_constr_name = datatype'_ext_constr_name @@ const_oid"
definition "datatype_in = \<open>in\<close>"

subsection\<open>Main Combinators for the Translation\<close>

text\<open>
As general remark, all the future translating steps
(e.g., that will occur in @{file "Floor1_access.thy"})
will extensively use Isabelle expressions,
represented by its Meta-Model, for example lots of functions will use @{term "Term_app"}...
So the overall can be simplified by the use of polymorphic cartouches.
It looks feasible to add a new front-end for cartouches in @{theory "Init"}
supporting the use of Isabelle syntax in cartouches,
then we could obtain at the end a parsed Isabelle Meta-Model in Isabelle.\<close>

definition "map_class_arg_only_var = map_class_arg_only_var_gen (\<lambda>s e. Term_postunary s (Term_basic e))"
definition "map_class_arg_only_var' = map_class_arg_only_var'_gen (\<lambda>s e. Term_postunary s (Term_basic e))"
definition "map_class_arg_only_var'' = map_class_arg_only_var''_gen (\<lambda>s e. Term_postunary s (Term_basic e))"

definition "split_ty name = L.map (\<lambda>s. hol_split (s @@ String.isub name)) [datatype_ext_name, datatype_name]"

definition "start_map f = L.mapM (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> env.
  let design_analysis = D_ocl_semantics env
    ; base_attr = (if design_analysis = Gen_only_design then id else L.filter (\<lambda> (_, OclTy_object (OclTyObj (OclTyCore _) _)) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, L.map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') env)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> env. start_map f (fl (D_ocl_semantics env)) env)"
definition "start_map''''' f fl = (\<lambda> env. start_map f (fl (D_output_sorry_dirty env) (D_ocl_semantics env)) env)"
definition "start_map'''''' f fl = (\<lambda> env. start_map f (fl (\<lambda>s. (case D_output_header_thy env of
                                                                   Some (n_thy, _, _) \<Rightarrow>
                                                                     String.replace_chars
                                                                       (\<lambda> x. if x = CHR 0x5F then \<open>-\<close>
                                                                             else \<degree>x\<degree>)
                                                                       n_thy
                                                                 | None \<Rightarrow> \<open>\<close>) @@ s)
                                                         (D_ocl_semantics env)) env)"

definition "start_m_gen final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen2 base_attr f print expr)"
definition "start_m final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class base_attr f print expr)"
definition "start_m' final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class' base_attr print expr)"
definition "start_m'3_gen final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen3 base_attr id print expr)"


definition "activate_simp_optimization = True"

definition "prev_was_stop = (\<lambda> [] \<Rightarrow> True | x # _ \<Rightarrow> ignore_meta_header x)"

fun collect_meta_embed where
   "collect_meta_embed accu e =
    (\<lambda> (True, _) \<Rightarrow> rev accu
     | (_, []) \<Rightarrow> rev accu
     | (_, x # l_meta) \<Rightarrow> collect_meta_embed (x # accu) (prev_was_stop l_meta, l_meta)) e"

definition "bootstrap_floor l env =
 (let l_setup = \<lambda>f. META_boot_setup_env (Boot_setup_env (f env \<lparr> D_output_disable_thy := True
                                                               , D_output_header_thy := None \<rparr>))
                    # l in
  ( if D_output_auto_bootstrap env then
      if prev_was_stop (D_input_meta env) then
        l
      else
        l_setup (\<lambda>env. compiler_env_config_reset_no_env env
                         \<lparr> D_input_meta := collect_meta_embed [] (False, D_input_meta env) \<rparr>)
    else
      META_boot_generation_syntax (Boot_generation_syntax (D_ocl_semantics env))
      # l_setup id
  , env \<lparr> D_output_auto_bootstrap := True \<rparr> ))"

definition "wrap_oclty x = \<open>\<cdot>\<close> @@ x"
definition "Term_annot_ocl e s = Term_annot' e (wrap_oclty s)"
definition "Term_oclset l = (case l of [] \<Rightarrow> Term_basic [\<open>Set{}\<close>] | _ \<Rightarrow> Term_paren \<open>Set{\<close> \<open>}\<close> (term_binop \<open>,\<close> l))"

context SML
begin
definition "oid s = (\<lambda>Oid n \<Rightarrow> basic [s @@ String.natural_to_digit10 n])"
end

lemmas [code] =
  (*def*)
  SML.oid_def

definition "Term_oid s = (\<lambda>Oid n \<Rightarrow> Term_basic [s @@ String.natural_to_digit10 n])"

subsection\<open>Preliminaries on: Enumeration\<close>

subsection\<open>Preliminaries on: Infrastructure\<close>

fun print_infra_type_synonym_class_rec_aux0 where
   "print_infra_type_synonym_class_rec_aux0 e =
   (let option = \<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [x] in
     (\<lambda> OclTy_collection c t \<Rightarrow>
          let (name, ty) = print_infra_type_synonym_class_rec_aux0 t in
          ( (if is_sequence c then \<open>Sequence\<close> else \<open>Set\<close>) @@ \<open>_\<close> @@ name
          , Typ_apply (Typ_base (if is_sequence c then var_Sequence_base else var_Set_base)) [ty])
      | OclTy_pair t1 t2 \<Rightarrow>
          let (name1, ty1) = print_infra_type_synonym_class_rec_aux0 t1
            ; (name2, ty2) = print_infra_type_synonym_class_rec_aux0 t2 in
          ( \<open>Pair\<close> @@ \<open>_\<close> @@ name1 @@ \<open>_\<close> @@ name2
          , Typ_apply (Typ_base var_Pair_base) [ty1, ty2])
      | OclTy_object (OclTyObj (OclTyCore_pre s) _) \<Rightarrow> (s, option (option (Typ_base (datatype_name @@ String.isub s))))
      | t \<Rightarrow> (str_of_ty t, Typ_base (str_of_ty t @@ String.isub \<open>base\<close>))) e)"

definition "print_infra_type_synonym_class_rec_aux t =
 (let (tit, body) = print_infra_type_synonym_class_rec_aux0 t in
  (tit, Typ_apply (Typ_base \<open>val\<close>) [Typ_base \<open>\<AA>\<close>, body]))"

definition "pref_generic_enum name_ty = name_ty @@ String.isub \<open>generic\<close>"

subsection\<open>Preliminaries on: AsType\<close>

definition "print_astype_from_universe_name name = S.flatten [const_oclastype, String.isub name, \<open>_\<AA>\<close>]"

subsection\<open>Preliminaries on: IsTypeOf\<close>

definition "print_istypeof_defined_name isub_name h_name = S.flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name, \<open>_defined\<close>]"
definition "print_istypeof_defined'_name isub_name h_name = S.flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name, \<open>_defined'\<close>]"
definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = S.flatten [\<open>down_cast_type\<close>, String.isub name_mid, \<open>_from_\<close>, name_any, \<open>_to_\<close>, name_pers]"

subsection\<open>Preliminaries on: IsKindOf\<close>

definition "print_iskindof_up_eq_asty_name name = (S.flatten [\<open>actual_eq_static\<close>, String.isub name])"
definition "print_iskindof_up_larger_name name_pers name_any = S.flatten [\<open>actualKind\<close>, String.isub name_pers, \<open>_larger_staticKind\<close>, String.isub name_any]"

subsection\<open>Preliminaries on: AllInstances\<close>

definition "gen_pre_post0 f_tit f_assum spec f_lemma meth_last =
  (let b = \<lambda>s. Term_basic [s]
     ; d = hol_definition
     ; f_allinst = \<lambda>s. \<open>OclAllInstances_\<close> @@ s
     ; f_tit = f_tit o f_allinst
     ; var_pre_post = \<open>pre_post\<close>
     ; var_mk = \<open>mk\<close>
     ; var_st = \<open>st\<close>
     ; s_generic = \<open>generic\<close>
     ; lem_gen = f_tit s_generic
     ; mk_pre_post = \<lambda>pre_post at_when f_cpl.
         let s_allinst = f_allinst at_when in
         Lemma_assumes
           (f_tit at_when)
           f_assum
           (spec (Term_app s_allinst) f_cpl pre_post)
           [C.unfolding [T.thm (d s_allinst)]]
           (C.by (M.rule (T.thm lem_gen) # meth_last)) in
  [ f_lemma lem_gen f_assum (spec (\<lambda>l. Term_app (f_allinst s_generic) (b var_pre_post # l)) (\<lambda>e. Term_app var_mk [e]) var_pre_post) var_pre_post var_mk var_st
  , mk_pre_post \<open>snd\<close> \<open>at_post\<close> (Term_pair (b var_st))
  , mk_pre_post \<open>fst\<close> \<open>at_pre\<close> (\<lambda>e. Term_pair e (b var_st)) ])"

definition "gen_pre_post f_tit spec f_lemma = gen_pre_post0 f_tit [] spec (\<lambda>lem_gen _. f_lemma lem_gen)"

subsection\<open>Preliminaries on: Accessor\<close>

definition "print_access_oid_uniq_name' name_from_nat isub_name attr = S.flatten [ isub_name var_oid_uniq, \<open>_\<close>, String.natural_to_digit10 name_from_nat, \<open>_\<close>, attr ]"
definition "print_access_oid_uniq_name name_from_nat isub_name attr = print_access_oid_uniq_name' name_from_nat isub_name (String.isup attr)"
definition "print_access_oid_uniq_mlname name_from_nat name attr = S.flatten [ var_oid_uniq, name, \<open>_\<close>, String.natural_to_digit10 name_from_nat, \<open>_\<close>, attr ]"

definition "print_access_choose_name n i j =
  S.flatten [var_switch, String.isub (String.natural_to_digit10 n), \<open>_\<close>, String.natural_to_digit10 i, String.natural_to_digit10 j]"
definition "print_access_choose_mlname n i j =
  S.flatten [var_switch, String.natural_to_digit10 n, \<open>_\<close>, String.natural_to_digit10 i, String.natural_to_digit10 j]"

definition "print_access_dot_consts_ty attr_ty =
              (let ty_base = \<lambda>attr_ty.
                 Typ_apply (Typ_base \<open>val\<close>) [Typ_base \<open>\<AA>\<close>,
                    let option = \<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [x] in
                    option (option (Typ_base attr_ty))] in
               case attr_ty of
                  OclTy_raw attr_ty \<Rightarrow> ty_base attr_ty
                | OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
                    let ty_obj = TyObj_to ty_obj
                      ; name = TyObjN_role_ty ty_obj
                      ; obj_mult = TyObjN_role_multip ty_obj in
                    Typ_base (if single_multip obj_mult then
                               wrap_oclty name
                             else if is_sequence obj_mult then
                               print_infra_type_synonym_class_sequence_name name
                             else
                               print_infra_type_synonym_class_set_name name)
                | OclTy_object (OclTyObj (OclTyCore_pre s) _) \<Rightarrow> Raw (wrap_oclty s)
                | OclTy_base_unlimitednatural \<Rightarrow> str_hol_of_ty_all Typ_apply ty_base attr_ty
                   (* REMARK Dependencies to UnlimitedNatural.thy can be detected and added
                             so that this pattern clause would be merged with the default case *)
                | OclTy_collection _ _ \<Rightarrow> Raw (fst (print_infra_type_synonym_class_rec_aux attr_ty))
                | OclTy_pair _ _ \<Rightarrow> Raw (fst (print_infra_type_synonym_class_rec_aux attr_ty))
                | _ \<Rightarrow> Raw (str_of_ty attr_ty))"

subsection\<open>Preliminaries on: Example (Floor 1)\<close>

datatype reporting = Warning
                   | Error
                   | Writeln

definition "raise_ml l_out s = SML (SML.app0 \<open>Ty'.check\<close>
    [ SML.list'
        (\<lambda>(rep, s).
          SML.pair (SML.basic [S.flatten [ \<open>META.\<close>
                                           , case rep of Warning \<Rightarrow> \<open>Warning\<close>
                                                       | Error \<Rightarrow> \<open>Error\<close>
                                                       | Writeln \<Rightarrow> \<open>Writeln\<close> ]])
                     (SML.string s))
        l_out
    , SML.string s ])"

definition "print_examp_def_st_inst_var_name ocli name = S.flatten [case Inst_name ocli of Some n \<Rightarrow> n, name]"

subsection\<open>Preliminaries on: Example (Floor 2)\<close>

subsection\<open>Preliminaries on: Context (Floor 1)\<close>

definition "print_ctxt_const_name attr_n var_at_when_hol name =
  S.flatten [ \<open>dot\<close>, String.isup attr_n, var_at_when_hol] @@ (case name of None \<Rightarrow> \<open>\<close> | Some name \<Rightarrow> \<open>_\<close> @@ name)"
definition "print_ctxt_pre_post_name attr_n var_at_when_hol name = hol_definition (print_ctxt_const_name attr_n var_at_when_hol name)"
definition "print_ctxt_inv_name n tit var_at_when = S.flatten [n, \<open>_\<close>, tit, var_at_when]"

definition "make_ctxt_free_var pref ctxt =
 (var_self # L.flatten [ L.map fst (Ctxt_fun_ty_arg ctxt)
                          , if pref = OclCtxtPre then [] else [var_result] ])"

subsection\<open>Preliminaries on: Context (Floor 2)\<close>

end
