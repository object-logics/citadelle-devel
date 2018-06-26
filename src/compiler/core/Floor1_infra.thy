(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Floor1_infra.thy ---
 * This file is part of HOL-TestGen.
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

section\<open>Main Translation for: Infrastructure\<close>

theory  Floor1_infra
imports Core_init
begin

definition "print_infra_enum_synonym _ env = (\<lambda>f. (f (fst (find_class_ass env)), env))
 (L.flatten o L.map
   (\<lambda> META_class_synonym (OclClassSynonym n1 n2) \<Rightarrow>
        [ O.type_synonym (Type_synonym' (pref_ty_syn n1) (Typ_base (str_hol_of_ty_all (\<lambda>a _. a) id n2))) ]
    | _ \<Rightarrow> []))"

definition "print_infra_datatype_class_1 = start_map'' O.datatype o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = L.map ((\<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [str_hol_of_ty_all Typ_apply Typ_base x]) o snd) in
    [ Datatype'
        (isub_name datatype_ext_name)
        (  (L.rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ String.isub x)])) (of_sub l_cons))
        @@@@ [(isub_name datatype_ext_constr_name, Raw const_oid # L.maps map_ty l_inherited)])
    , Datatype'
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, Raw (isub_name datatype_ext_name) # map_ty l_attr ) ] ]) expr)"

definition \<open>print_latex_infra_datatype_class = start_map'' O.datatype o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = L.map ((\<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [str_hol_of_ty_all Typ_apply Typ_base x]) o snd)
      ; n1 = \<open>{ext}\<close>
      ; n2 = \<open>{ty}\<close> in
    [ Datatype'
        (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n1 @@ \<open>\<close>)
        (  (L.rev_map (\<lambda>x. ( \<open>\operatorname{mk}_\text{\<close> @@ name @@ \<open>\_\<close> @@ x @@ \<open>}\<close>
                         , [Raw (\<open>\operatorname{\<close> @@ x @@ \<open>}_\<close> @@ n2 @@ \<open>\<close>)])) (of_sub l_cons))
        @@@@ [(\<open>\operatorname{mk}_\text{\<close> @@ name @@ \<open>}\<close>, Raw const_oid # L.maps map_ty l_inherited)])
    , Datatype'
        (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n2 @@ \<open>\<close>)
        [ (\<open>\operatorname{mkoid}_\text{\<close> @@ name @@ \<open>}\<close>, Raw (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n1 @@ \<open>\<close>) # map_ty l_attr ) ] ]) expr)\<close>

definition "print_infra_datatype_class_2 = start_map'' O.datatype o (\<lambda>expr _ base_attr' _. map_class_gen_h'''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = L.map ((\<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [str_hol_of_ty_all Typ_apply Typ_base x]) o snd)
      ; l =
    [ Datatype'
        (isub_name datatype'_ext'_name)
        ([(isub_name datatype'_ext_constr_name, L.flatten [ map_ty l_attr
                                                          , if l_cons = [] then [] else [ Opt (isub_name datatype'_ext_name) ]])])
    , Datatype'
        (isub_name datatype'_name)
        [(isub_name datatype'_constr_name, L.flatten [ Raw const_oid # L.maps map_ty l_inherited
                                                     , [ Raw (isub_name datatype'_ext'_name) ]])]] in
    if l_cons = [] then l
    else
      Datatype'
        (isub_name datatype'_ext_name)
        (L.rev_map (\<lambda> OclClass x _ _ \<Rightarrow>
                        ( datatype'_ext_constr_name @@ mk_constr_name name x
                        , [Raw (datatype'_ext'_name @@ String.isub x)])) l_cons) # l) expr)"

definition "print_infra_datatype_equiv_2of1_name = \<open>class_ty_ext_equiv_2of1\<close>"
definition "print_infra_datatype_equiv_2of1_name_aux = print_infra_datatype_equiv_2of1_name @@ \<open>_aux\<close>"
definition "print_infra_datatype_equiv_2of1 = start_map'' O.definition o (\<lambda>expr _ base_attr' _. map_class_gen_h'''
 (\<lambda>isub_name name _ l_attr l_inherited next_dataty.
  let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
    ; f_attr_own = (\<lambda>s. \<open>own\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; f_attr_inh = (\<lambda>s. \<open>inh\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; (l_attr, l_inherited) = (L.map f_attr_own l_attr, L.map f_attr_inh (L.flatten l_inherited))
    ; a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; a' = \<lambda>f l. Term_app f (L.map b l)
    ; print_name = isub_name print_infra_datatype_equiv_2of1_name_aux
    ; var_oid = \<open>oid\<close>
    ; f_pat = \<lambda>l. L.flatten [var_oid # l_inherited, l] in
  L.map (\<lambda> (n,d). Definition (Term_rewrite (b n) \<open>=\<close> d))
  [( print_name
   , let var_t = \<open>t\<close> in
     Term_lambdas
       (f_pat [])
       (Term_function
         [( a' (isub_name datatype'_ext_constr_name) (L.flatten [ l_attr, if next_dataty = [] then [] else [var_t]])
          , Term_app
              (isub_name datatype_constr_name)
              ( (let pat_none = a' (isub_name datatype_ext_constr_name) (f_pat []) in
                 if next_dataty = [] then pat_none
                 else
                   Term_case
                    (b var_t)
                    ( (b \<open>None\<close>, pat_none)
                    # (L.map
                        (\<lambda> OclClass name_pers l_attr_pers name_pers0 \<Rightarrow>
                          let l_attr_pers = L.map f_attr_own (fst (base_attr' (l_attr_pers, [])))
                            ; isub_name_pers = \<lambda>x. x @@ String.isub name_pers in
                          ( Term_some (a (datatype'_ext_constr_name @@ mk_constr_name name name_pers) (b var_t))
                          , let f_pat = \<lambda>l. L.flatten [ l_attr, l_inherited, l] in
                            Term_case
                              (a' (isub_name_pers print_infra_datatype_equiv_2of1_name_aux) (var_oid # f_pat [var_t]))
                              (let a_pers = \<lambda>x. Term_app (isub_name_pers datatype_constr_name)
                                                         (x # L.map b l_attr_pers)
                                 ; v = a_pers (a' (isub_name_pers datatype_ext_constr_name)
                                                  (var_oid # f_pat [])) in
                               (v, a (datatype_ext_constr_name @@ mk_constr_name name name_pers) v)
                               #
                               L.map
                                 (\<lambda> OclClass name_bot _ _ \<Rightarrow>
                                   ( a_pers (a (datatype_ext_constr_name @@ mk_constr_name name_pers name_bot)
                                               (b var_t))
                                   , a (datatype_ext_constr_name @@ mk_constr_name name name_bot) (b var_t)))
                                 (get_class_hierarchy_strict name_pers0))))
                        next_dataty)))
              # L.map b l_attr))]))
  , ( isub_name print_infra_datatype_equiv_2of1_name
    , Term_function [ let l = L.map b (f_pat [\<open>t\<close>]) in
                      (Term_app (isub_name datatype'_constr_name) l, Term_app print_name l)])]) expr)"

definition "print_infra_datatype_equiv_1of2_name = \<open>class_ty_ext_equiv_1of2\<close>"
definition "print_infra_datatype_equiv_1of2_name_aux0 = print_infra_datatype_equiv_1of2_name @@ \<open>_aux0\<close>"
definition "print_infra_datatype_equiv_1of2_name_aux = print_infra_datatype_equiv_1of2_name @@ \<open>_aux\<close>"
definition "print_infra_datatype_equiv_1of2_name_get_oid_inh = print_infra_datatype_equiv_1of2_name @@ \<open>_get_oid_inh\<close>"
definition "print_infra_datatype_equiv_1of2 = start_map'' O.definition o (\<lambda>expr _ base_attr' _. map_class_gen_h'''
 (\<lambda>isub_name name _ l_attr l_inherited next_dataty.
  let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
    ; f_attr_own = (\<lambda>s. \<open>own\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; f_attr_inh = (\<lambda>s. \<open>inh\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; f_attr_var = (\<lambda>s. \<open>var\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; (l_attr', l_attr, l_inherited', l_inherited) =
        ( L.map f_attr_var l_attr
        , L.map f_attr_own l_attr
        , L.map f_attr_var (L.flatten l_inherited)
        , L.map f_attr_inh (L.flatten l_inherited))
    ; a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; a' = \<lambda>f l. Term_app f (L.map b l)
    ; print_name = isub_name print_infra_datatype_equiv_1of2_name_aux
    ; var_t = \<open>t\<close>
    ; var_tt = \<open>tt\<close>
    ; var_oid = \<open>oid\<close> in
  L.map (\<lambda> (n,d). Definition (Term_rewrite (b n) \<open>=\<close> d))
  [ ( isub_name print_infra_datatype_equiv_1of2_name_get_oid_inh
    , Term_function
        ((a' (isub_name datatype_ext_constr_name) (L.flatten [[var_oid], l_inherited])
                     ,Term_pairs' b (L.flatten [[var_oid], l_inherited]))
         #
         (L.flatten
           (L.map
             (fst o fold_class (\<lambda>isub_name_pers name_pers l_attr_pers l_inh _ _.
               let l_attr_pers = L.map f_attr_var (fst (base_attr' (l_attr_pers, []))) in
               Pair ( a (datatype_ext_constr_name @@ mk_constr_name name name_pers)
                        (a' (isub_name_pers datatype_constr_name) (var_t # l_attr_pers))
                    , Term_case (a (isub_name_pers print_infra_datatype_equiv_1of2_name_get_oid_inh) (b var_t))
                                [ let l_inh = L.flatten [ L.flatten (L.map (\<lambda>OclClass _ l_attr _ \<Rightarrow>
                                                                             L.map f_attr_var (fst (base_attr' (l_attr, [])))) (of_inh l_inh))
                                                        , l_attr'
                                                        , l_inherited' ] in
                                  (Term_pairs' b (var_oid # l_inh), Term_pairs' b (var_oid # l_inherited'))])) ())
             next_dataty))))
  , ( print_name
    , Term_function
        [( a' (isub_name datatype_constr_name) (var_t # l_attr)
         , Term_app
             (isub_name datatype'_ext_constr_name)
             (L.flatten
               [ L.map b l_attr
               , if next_dataty = [] then [] else
                 [Term_case (b var_t)
                  ( (a' (isub_name datatype_ext_constr_name) (var_oid # l_inherited), b \<open>None\<close>)
                    #
                    L.flatten (L.map (fst o fold_class (\<lambda>isub_name_pers name_pers l_attr_pers l_inh _ _.
                      let l_attr_pers = L.map f_attr_var (fst (base_attr' (l_attr_pers, []))) in
                      Pair
                       ( a (datatype_ext_constr_name @@ mk_constr_name name name_pers) (b var_tt)
                       , Term_case
                           (Term_case (b var_tt)
                             [ let var_t = \<open>t\<close> in
                               ( a' (isub_name_pers datatype_constr_name) (var_t # l_attr_pers)
                               , a (isub_name_pers print_infra_datatype_equiv_1of2_name_get_oid_inh) (b var_t))])
                           [(Term_pairs'
                               b
                               ( var_oid # (L.flatten [ L.flatten (L.map (\<lambda>OclClass _ l_attr _ \<Rightarrow>
                                                          L.map f_attr_var (fst (base_attr' (l_attr, [])))) (of_inh l_inh))
                                                      , l_attr'
                                                      , l_inherited']))
                               , let f_cons = \<lambda> expr name0 name1. Term_some (a (datatype'_ext_constr_name @@ mk_constr_name name1 name0) expr)
                                   ; (expr, name0) =
                                   foldl
                                     (\<lambda> (expr, name0) (name1, l_attr1).
                                       ( Term_app (datatype'_ext_constr_name @@ String.isub name1)
                                                  (L.flatten [L.map b (L.map f_attr_var (fst (base_attr' (l_attr1, [])))), [f_cons expr name0 name1]])
                                       , name1))
                                     (a (isub_name_pers print_infra_datatype_equiv_1of2_name_aux) (b var_tt), name_pers)
                                     (L.map (\<lambda>OclClass n l_attr _ \<Rightarrow> (n, l_attr)) (of_inh l_inh)) in
                                 f_cons expr name0 name)])) ()) next_dataty)) ]]))])
  , ( isub_name print_infra_datatype_equiv_1of2_name
    , Term_function
        [( a' (isub_name datatype_constr_name) (var_t # l_attr)
         , Term_case
             (a (isub_name print_infra_datatype_equiv_1of2_name_get_oid_inh) (b var_t))
             [( Term_pairs' b (var_oid # l_inherited)
              , Term_app (isub_name datatype'_constr_name)
                         (L.flatten [ L.map b (var_oid # l_inherited)
                                    , [a print_name (a' (isub_name datatype_constr_name) (var_t # l_attr))]]))])])]) expr)"

definition "print_infra_datatype_equiv_1_idempo_name = \<open>class_ty_ext_equiv_1_idempo\<close>"
definition "print_infra_datatype_equiv_1_idempo = start_map'' O.lemma o (\<lambda>expr _ base_attr' _. map_class_gen_h'''
 (\<lambda>isub_name name _ l_attr l_inherited next_dataty.
  let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
    ; f_attr_own = (\<lambda>s. \<open>own\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; f_attr_inh = (\<lambda>s. \<open>inh\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; f_attr_var = (\<lambda>s. \<open>var\<close> @@ String.isub s (* fresh variable names *)) o fst
    ; (l_attr', l_attr, l_inherited', l_inherited) =
        ( L.map f_attr_var l_attr
        , L.map f_attr_own l_attr
        , L.map f_attr_var (L.flatten l_inherited)
        , L.map f_attr_inh (L.flatten l_inherited))
    ; a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; f_1of2 = isub_name print_infra_datatype_equiv_1of2_name
    ; f_2of1 = isub_name print_infra_datatype_equiv_2of1_name
    ; var_X = \<open>X\<close>
    ; var_t = \<open>t\<close>
    ; var_oid = \<open>oid\<close> in
  [ Lemma_assumes (isub_name print_infra_datatype_equiv_1_idempo_name)
      []
      (Term_rewrite (a f_1of2 (a f_2of1 (b var_X))) \<open>=\<close> (b var_X))
      [ C.apply [M.case_tac (b var_X), M.simp]
      (*, C.fix (var_oid # l_inherited')*)
      (* TODO below *) ]
      C.sorry ]) expr)"
(*
(*
Class Person < Planet   Attributes salary : Integer
Class Planet < Galaxy   Attributes wormhole : UnlimitedNatural
                                   weight : Integer
Class Galaxy            Attributes sound : Void
                                   moving : Boolean
Class Ooo < Ppp
Class Ppp < Planet
Class Yyy < Zzz
Class Zzz
*)
lemma class_ty_ext_equiv_1_idempo\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
shows "(class_ty_ext_equiv_1of2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((class_ty_ext_equiv_2of1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (X)))) = X"
 apply(case_tac "X", simp)
 subgoal for oid (*var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t*) var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g t
 apply(case_tac t, simp)
 subgoal for var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t opt
 apply(case_tac opt, simp)
 apply(subst class_ty_ext_equiv_1of2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_2of1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       auto)
 subgoal for obj
 apply(case_tac "obj", simp) defer apply(simp)
 subgoal for ty2\<E>\<X>\<T>\<^sub>P\<^sub>p\<^sub>p
 apply(insert class_ty_ext_equiv_1_idempo\<^sub>P\<^sub>p\<^sub>p[of "mk2oid\<^sub>P\<^sub>p\<^sub>p oid var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d
                                                          var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g ty2\<E>\<X>\<T>\<^sub>P\<^sub>p\<^sub>p"])
 apply(subst class_ty_ext_equiv_1of2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_2of1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       subst class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def,
       simp)

 apply(case_tac "class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>p\<^sub>p oid var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t
                                               var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g ty2\<E>\<X>\<T>\<^sub>P\<^sub>p\<^sub>p", simp)
 subgoal for ty\<E>\<X>\<T>\<^sub>P\<^sub>p\<^sub>p
  apply(case_tac ty\<E>\<X>\<T>\<^sub>P\<^sub>p\<^sub>p, simp)
  subgoal for ty\<^sub>O\<^sub>o\<^sub>o
   apply(case_tac ty\<^sub>O\<^sub>o\<^sub>o, simp)
    subgoal for ty\<E>\<X>\<T>\<^sub>O\<^sub>o\<^sub>o
     apply(case_tac "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>O\<^sub>o\<^sub>o ty\<E>\<X>\<T>\<^sub>O\<^sub>o\<^sub>o", simp)
    by(simp add: class_ty_ext_equiv_1of2\<^sub>P\<^sub>p\<^sub>p_def class_ty_ext_equiv_2of1\<^sub>P\<^sub>p\<^sub>p_def
                 class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>p\<^sub>p_def
                 class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>p\<^sub>p_def)
  done
 by(simp add: class_ty_ext_equiv_1of2\<^sub>P\<^sub>p\<^sub>p_def class_ty_ext_equiv_2of1\<^sub>P\<^sub>p\<^sub>p_def
              class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>p\<^sub>p_def
              class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>p\<^sub>p_def)
 done
sorry sorry sorry sorry
*)

definition "print_infra_datatype_universe expr = start_map O.datatype
  [ Datatype' \<open>\<AA>\<close>
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_enum_syn _ env = (\<lambda>f1 f2. (L.flatten [f1 (D_input_meta env), f2 (fst (find_class_ass env))], env))
 (L.flatten o L.map
    (\<lambda> META_enum (OclEnum name_ty _) \<Rightarrow>
         [O.type_synonym (Type_synonym' name_ty (Typ_apply (Typ_base (pref_generic_enum name_ty)) [Typ_base \<open>\<AA>\<close>]))]
     | _ \<Rightarrow> []))
 (L.flatten o L.map
    (\<lambda> META_class_synonym (OclClassSynonym name_ty ty) \<Rightarrow>
         [O.type_synonym (Type_synonym' name_ty (Typ_base (str_of_ty ty)))]
     | _ \<Rightarrow> []))"

definition "print_infra_type_synonym_class _ = start_map id
  (L.map O.type_synonym
    (let ty = \<lambda> t s. Type_synonym' (str_of_ty t) (Typ_apply (Typ_base s) [Typ_base \<open>\<AA>\<close>]) in
     (* base type *)
     ty OclTy_base_void ty_void #
     ty OclTy_base_boolean ty_boolean #
     ty OclTy_base_integer ty_integer #
     (*ty OclTy_base_unlimitednatural ty_unlimitednatural #*)
     ty OclTy_base_real ty_real #
     ty OclTy_base_string ty_string #
     (* *)
     Type_synonym'' var_val' [\<open>'\<alpha>\<close>] (\<lambda> [alpha] \<Rightarrow> Typ_apply (Typ_base \<open>val\<close>) [Typ_base \<open>\<AA>\<close>, Typ_base alpha ]) #
     [])
   @@@@
   L.map O.type_notation
     [ Type_notation var_val' \<open>\<cdot>(_)\<close> ])"

definition "print_infra_type_synonym_class_higher expr = start_map O.type_synonym
 (let option = Typ_apply_paren \<open>\<langle>\<close> \<open>\<rangle>\<^sub>\<bottom>\<close> in
  L.flatten
    (map_class
      (\<lambda>isub_name name _ _ _ _.
        [ Type_synonym' name
                       (option (option (Typ_base (isub_name datatype_name))))
        (*, Type_synonym' name (Typ_apply_paren \<open>\<cdot>\<close> \<open>\<close> (Typ_base (name @@ \<open>'\<close>)))*)])
      expr))"

definition "print_infra_type_synonym_class_rec = (\<lambda>expr env.
  map_prod id (\<lambda> D_ocl_HO_type. env \<lparr> D_ocl_HO_type := D_ocl_HO_type \<rparr>)
    (L.split (L.map (\<lambda>(tit, body). (O.type_synonym (Type_synonym' (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String tit) body), tit))
                          (snd (fold_class (\<lambda>_ _ l_attr _ _ _.
                                             Pair () o List.fold
                                               (\<lambda>(_, t) l.
                                                 let f = (* WARNING we may test with RBT instead of List *)
                                                         \<lambda>t l.
                                                           let (tit, body) = print_infra_type_synonym_class_rec_aux t in
                                                           if String.assoc tit l = None then (String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e tit, body) # l else l in
                                                 case t of
                                                   OclTy_object (OclTyObj (OclTyCore obj) _) \<Rightarrow>
                                                     let t = \<lambda>ty. OclTy_collection (ocl_multiplicity_ext [] None [ty] ()) (OclTy_class_pre (TyObjN_role_ty (TyObj_to obj))) in
                                                     f (t Sequence) (f (t Set) l)
                                                 | OclTy_collection _ _ \<Rightarrow> f t l
                                                 | OclTy_pair _ _ \<Rightarrow> f t l
                                                 | _ \<Rightarrow> l)
                                               l_attr)
                                           []
                                           expr)))))"

definition "print_infra_instantiation_class = start_map'' O.instantiation o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited) in
    let oid_of = \<open>oid_of\<close> in
    [Instantiation
      (isub_name datatype_name)
      oid_of
      (Term_rewrite
        (Term_basic [oid_of])
        \<open>=\<close>
        (Term_function
                   [ let var_oid = \<open>t\<close> in
                     ( Term_basic (isub_name datatype_constr_name # var_oid # L.map (\<lambda>_. wildcard) l_attr)
                     , Term_case
                         (Term_basic [var_oid])
                         ( ( Term_app
                               (isub_name datatype_ext_constr_name)
                               (Term_basic [var_oid] # L.flatten (L.map (L.map (\<lambda>_. Term_basic [wildcard])) l_inherited))
                           , Term_basic [var_oid])
                         # L.map (\<lambda>x. ( Term_app (datatype_ext_constr_name @@ mk_constr_name name x) [Term_basic [var_oid]]
                                         , Term_app oid_of [Term_basic [var_oid]])) (of_sub l_cons)))]))
    ]) expr)"

definition "print_infra_instantiation_universe expr = start_map O.instantiation
  [ let oid_of = \<open>oid_of\<close> in
    Instantiation \<open>\<AA>\<close> oid_of
      (Term_rewrite
        (Term_basic [oid_of])
        \<open>=\<close>
        (Term_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Term_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_instantia_def_strictrefeq_name mk_strict name = mk_strict [\<open>_\<close>, String.isub name]"
definition "print_instantia_def_strictrefeq = start_map O.overloading o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. S.flatten (\<open>StrictRefEq\<close> # String.isub \<open>Object\<close> # l))
      ; s_strict = mk_strict [\<open>_\<close>, String.isub name]
      ; var_x = \<open>x\<close>
      ; var_y = \<open>y\<close> in
    Overloading'
      \<open>StrictRefEq\<close>
      (Ty_arrow' (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty name)))))
      (print_instantia_def_strictrefeq_name mk_strict name)
      (Term_rewrite (Term_binop (Term_annot_ocl (Term_basic [var_x]) name)
                                \<open>\<doteq>\<close>
                                (Term_basic [var_y]))
                    \<open>\<equiv>\<close>
                    (Term_basic [mk_strict [], var_x, var_y])) )"

definition "print_instantia_lemmas_strictrefeq = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let mk_strict = (\<lambda>l. S.flatten (\<open>StrictRefEq\<close> # String.isub \<open>Object\<close> # l))
         ; name_set = map_class (\<lambda>_ name _ _ _ _. print_instantia_def_strictrefeq_name mk_strict name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
         [ Lemmas_simp \<open>\<close> (L.map (T.thm) name_set) ]
  else (\<lambda>_. []))"

end
