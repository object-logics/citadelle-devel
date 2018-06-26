(******************************************************************************
 * HOL-OCL
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

section\<open>Main Translation for: AllInstances\<close>

theory  Floor1_allinst
imports Core_init
begin

definition "print_allinst_def_id = start_map O.definition o
  map_class (\<lambda>isub_name name _ _ _ _.
    let const_astype = S.flatten [const_oclastype, String.isub name, \<open>_\<AA>\<close>] in
    Definition (Term_rewrite (Term_basic [name]) \<open>=\<close> (Term_basic [const_astype])))"

definition "print_allinst_lemmas_id = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let name_set = map_class (\<lambda>_ name _ _ _ _. name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
         [ Lemmas_simp \<open>\<close> (L.map (T.thm o hol_definition) name_set) ]
  else (\<lambda>_. []))"

definition "print_allinst_astype_name isub_name = S.flatten [isub_name const_oclastype, \<open>_\<AA>\<close>, \<open>_some\<close>]"
definition "print_allinst_astype = start_map O.lemma o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Term_basic [s]
    ; var_x = \<open>x\<close>
    ; d = hol_definition in
  [Lemma
    (print_allinst_astype_name isub_name)
    [ Term_rewrite
        (Term_app (S.flatten [isub_name const_oclastype, \<open>_\<AA>\<close>]) [b var_x])
        \<open>\<noteq>\<close>
        (b \<open>None\<close>)]
    []
    (C.by [M.simp_add [d (S.flatten [isub_name const_oclastype, \<open>_\<AA>\<close>])]])])"

definition "print_allinst_exec = start_map O.lemma o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Term_basic [s]
    ; a = \<lambda>f x. Term_app f [x]
    ; d = hol_definition
    ; f = Term_paren \<open>\<lfloor>\<close> \<open>\<rfloor>\<close>
    ; f_img = \<lambda>e1. Term_binop (b e1) \<open>`\<close>
    ; ran_heap = \<lambda>var_pre_post var_tau. f_img name (a \<open>ran\<close> (a \<open>heap\<close> (Term_app var_pre_post [b var_tau])))
    ; f_incl = \<lambda>v1 v2.
        let var_tau = \<open>\<tau>\<close> in
        Term_bind \<open>\<And>\<close> (b var_tau) (Term_binop (Term_applys (Term_pat v1) [b var_tau]) \<open>\<subseteq>\<close> (Term_applys (Term_pat v2) [b var_tau]))
    ; var_B = \<open>B\<close>
    ; var_C = \<open>C\<close> in
  gen_pre_post
    (\<lambda>s. S.flatten [isub_name s, \<open>_exec\<close>])
    (\<lambda>f_expr _ var_pre_post.
      Term_rewrite
       (f_expr [b name])
       \<open>=\<close>
       (Term_lam \<open>\<tau>\<close> (\<lambda>var_tau. Term_app var_Abs_Set [f (f (f_img \<open>Some\<close> (ran_heap var_pre_post var_tau))) ])))
    (\<lambda>lem_tit lem_spec var_pre_post _ _.
      Lemma_assumes
        lem_tit
        []
        lem_spec
        (let var_S1 = \<open>S1\<close>
           ; var_S2 = \<open>S2\<close> in
         [ C.let' (Term_pat var_S1) (Term_lam \<open>\<tau>\<close> (ran_heap var_pre_post))
         , C.let' (Term_pat var_S2) (Term_lam \<open>\<tau>\<close> (\<lambda>var_tau. Term_binop (Term_applys (Term_pat var_S1) [b var_tau]) \<open>-\<close> (Term_paren \<open>{\<close> \<open>}\<close> (b \<open>None\<close>))))
         , C.have var_B (f_incl var_S2 var_S1) (C.by [M.auto])
         , C.have var_C (f_incl var_S1 var_S2) (C.by [M.auto_simp_add [print_allinst_astype_name isub_name]])
         , C.apply [M.simp_add_del [d \<open>OclValid\<close>] [d \<open>OclAllInstances_generic\<close>, S.flatten [isub_name const_ocliskindof, \<open>_\<close>, name]]] ])
        (C.by [M.insert [T.OF_l (T.thm \<open>equalityI\<close>) (L.map T.thm [var_B, var_C])], M.simp]))
    [])"

definition "print_allinst_istypeof_pre_name1 = \<open>ex_ssubst\<close>"
definition "print_allinst_istypeof_pre_name2 = \<open>ex_def\<close>"
definition "print_allinst_istypeof_pre = start_map O.lemma o (\<lambda>_.
  [ Lemma
      print_allinst_istypeof_pre_name1
      (let var_x = \<open>x\<close>
         ; var_B = \<open>B\<close>
         ; var_s = \<open>s\<close>
         ; var_t = \<open>t\<close>
         ; var_P = \<open>P\<close>
         ; b = \<lambda>s. Term_basic [s]
         ; a = \<lambda>f x. Term_app f [x]
         ; bind = \<lambda>symb. Term_bind symb (Term_binop (b var_x) \<open>\<in>\<close> (b var_B))
         ; f = \<lambda>v. bind \<open>\<exists>\<close> (a var_P (a v (b var_x))) in
       [ Term_bind \<open>\<forall>\<close> (Term_binop (b var_x) \<open>\<in>\<close> (b var_B)) (Term_rewrite (a var_s (b var_x)) \<open>=\<close> (a var_t (b var_x)))
       , Term_rewrite (f var_s) \<open>=\<close> (f var_t) ])
      []
      (C.by [M.simp])
  , Lemma
      print_allinst_istypeof_pre_name2
      (let var_x = \<open>x\<close>
         ; var_X = \<open>X\<close>
         ; var_y = \<open>y\<close>
         ; b = \<lambda>s. Term_basic [s]
         ; c = Term_paren \<open>\<lceil>\<close> \<open>\<rceil>\<close>
         ; f = Term_paren \<open>\<lfloor>\<close> \<open>\<rfloor>\<close>
         ; p = Term_paren \<open>{\<close> \<open>}\<close> in
       [ Term_binop (b var_x) \<open>\<in>\<close> (c (c (f (f (Term_binop (b \<open>Some\<close>) \<open>`\<close> (Term_parenthesis (Term_binop (b var_X) \<open>-\<close> (p (b \<open>None\<close>)))))))))
       , Term_bind \<open>\<exists>\<close> (b var_y) (Term_rewrite (b var_x) \<open>=\<close> (f (f (b var_y)))) ])
      []
      (C.by [M.auto_simp_add []]) ])"

definition "print_allinst_istypeof_single isub_name name isub_name2 name2 const_oclisof dot_isof f_simp1 f_simp2 =
  (let b = \<lambda>s. Term_basic [s]
    ; d = hol_definition
    ; s = M.subst_l [\<open>1\<close>,\<open>2\<close>,\<open>3\<close>]
    ; var_tau = \<open>\<tau>\<close> in
  gen_pre_post
    (\<lambda>s. S.flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name2 const_oclisof])
    (\<lambda>f_expr _ _. Term_binop (b var_tau) \<open>\<Turnstile>\<close> (Term_app var_OclForall_set [f_expr [b name], b (isub_name2 const_oclisof) ]))
    (\<lambda>lem_tit lem_spec _ _ _. Lemma
      lem_tit
      [lem_spec]
      [ [M.simp_add_del [d \<open>OclValid\<close>] (d \<open>OclAllInstances_generic\<close> # f_simp1 [S.flatten [isub_name2 const_oclisof, \<open>_\<close>, name]])]
      , [M.simp_only (L.flatten [L.map T.thm [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [T.simplified (T.thm \<open>OclAllInstances_generic_defined\<close>) (T.thm (d \<open>OclValid\<close>))]])]
      , [M.simp_only [T.thm (d \<open>OclAllInstances_generic\<close>)]]
      , [s (T.thm var_Abs_Set_inverse), M.simp_add [d \<open>bot_option\<close>]]
      , [s (T.where
             (T.thm print_allinst_istypeof_pre_name1)
             [ (\<open>s\<close>, Term_lam \<open>x\<close> (\<lambda>var_x. Term_applys (Term_postunary (Term_lambda wildcard (b var_x)) (b (dot_isof name2))) [b var_tau]))
             , (\<open>t\<close>, Term_lambda wildcard (Term_app \<open>true\<close> [b var_tau]))])]
      , [M.intro [ T.thm \<open>ballI\<close>
                   , T.simplified_l
                       (T.thm (if name = name2 then
                                   print_iskindof_up_eq_asty_name name
                                 else
                                   print_iskindof_up_larger_name name name2))
                       (L.map T.thm (d \<open>OclValid\<close> # f_simp2 [S.flatten [isub_name const_ocliskindof, \<open>_\<close>, name]]))]]
      , [M.drule (T.thm print_allinst_istypeof_pre_name2), M.erule (T.thm (\<open>exE\<close>)), M.simp]]
      (C.by [M.simp]))
      [])"

definition "print_allinst_istypeof = start_map'' O.lemma o (\<lambda>expr base_attr _ _. map_class_gen (\<lambda>isub_name name l_attr _ _ next_dataty.
  let l_attr = base_attr l_attr in
  let b = \<lambda>s. Term_basic [s]
    ; d = hol_definition
    ; s = M.subst_l [\<open>1\<close>,\<open>2\<close>,\<open>3\<close>]
    ; var_tau = \<open>\<tau>\<close> in
  case next_dataty of [] \<Rightarrow>
    print_allinst_istypeof_single isub_name name isub_name name const_oclistypeof dot_istypeof (\<lambda>_. []) id
  | OclClass name_next _ _ # _ \<Rightarrow>
    L.flatten
    [ gen_pre_post
        (\<lambda>s. S.flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name const_oclistypeof, \<open>1\<close>])
        (\<lambda>f_expr _ _.
           Term_exists
             \<open>\<tau>\<close>
             (\<lambda>var_tau. Term_binop (b var_tau) \<open>\<Turnstile>\<close> (Term_app var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_assumes
           lem_tit
           [(\<open>\<close>, True, Term_And \<open>x\<close> (\<lambda>var_x. Term_rewrite (Term_app var_pre_post [Term_parenthesis (Term_binop (b var_x) \<open>,\<close> (b var_x))]) \<open>=\<close> (b var_x)) )]
           lem_spec
           (L.map C.apply
              [ let var_tau0 = var_tau @@ String.isub \<open>0\<close> in
                [M.rule (T.where (T.thm \<open>exI\<close>) [(\<open>x\<close>, b var_tau0)]), M.simp_add_del (L.map d [var_tau0, \<open>OclValid\<close>]) [d \<open>OclAllInstances_generic\<close>]]
              , [M.simp_only (L.flatten [L.map T.thm [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [T.simplified (T.thm \<open>OclAllInstances_generic_defined\<close>) (T.thm (d \<open>OclValid\<close>))]])]
              , [M.simp_only [T.thm (d \<open>OclAllInstances_generic\<close>)]]
              , [s (T.thm var_Abs_Set_inverse), M.simp_add [d \<open>bot_option\<close>]] ] )
           (C.by [M.simp (*M.simp_add [S.flatten [isub_name const_oclistypeof, \<open>_\<close>, name]]*)]))
        [M.simp]
    , gen_pre_post
        (\<lambda>s. S.flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name const_oclistypeof, \<open>2\<close>])
        (\<lambda>f_expr _ _.
           Term_exists
             \<open>\<tau>\<close>
             (\<lambda>var_tau. Term_binop (b var_tau) \<open>\<Turnstile>\<close> (Term_app \<open>not\<close> [Term_app var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ]])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_assumes
           lem_tit
           [(\<open>\<close>, True, Term_And \<open>x\<close> (\<lambda>var_x. Term_rewrite (Term_app var_pre_post [Term_parenthesis (Term_binop (b var_x) \<open>,\<close> (b var_x))]) \<open>=\<close> (b var_x)) )]
           lem_spec
           (let var_oid = \<open>oid\<close>
              ; var_a = \<open>a\<close>
              ; var_t0 = \<open>t0\<close>
              ; s_empty = \<open>Map.empty\<close> in
            [ C.fix [var_oid, var_a]
            , C.let' (Term_pat var_t0) (Term_app \<open>state.make\<close>
                [ Term_app s_empty [Term_binop (b var_oid) \<open>\<mapsto>\<close> (Term_app (isub_name datatype_in) [Term_app (isub_name datatype_constr_name) (Term_app (datatype_ext_constr_name @@ mk_constr_name name name_next) [b var_a] # L.map (\<lambda>_. b \<open>None\<close>) l_attr)])]
                , b s_empty])
            , C.apply [M.rule (T.where (T.thm \<open>exI\<close>) [(\<open>x\<close>, Term_parenthesis (Term_binop (Term_pat var_t0) \<open>,\<close> (Term_pat var_t0)))]), M.simp_add_del [d \<open>OclValid\<close>] [d \<open>OclAllInstances_generic\<close>]]
            , C.apply [M.simp_only (L.flatten [L.map T.thm [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [T.simplified (T.thm \<open>OclAllInstances_generic_defined\<close>) (T.thm (d \<open>OclValid\<close>))]])]
            , C.apply [M.simp_only (L.map (\<lambda>x. T.thm (d x)) [\<open>OclAllInstances_generic\<close>, S.flatten [isub_name const_oclastype, \<open>_\<AA>\<close>]])]
            , C.apply [s (T.thm var_Abs_Set_inverse), M.simp_add [d \<open>bot_option\<close>]] ] )
           (C.by [M.simp_add [d \<open>state.make\<close>, d \<open>OclNot\<close>]]))
        [M.simp]]) expr)"

definition "print_allinst_iskindof_eq = start_map O.lemma o map_class_gen (\<lambda>isub_name name _ _ _ _.
  print_allinst_istypeof_single isub_name name isub_name name const_ocliskindof dot_iskindof id (\<lambda>_. []))"

definition "print_allinst_iskindof_larger = start_map O.lemma o L.flatten o map_class_nupl2'_inh (\<lambda>name name2.
  print_allinst_istypeof_single (\<lambda>s. s @@ String.isub name) name (\<lambda>s. s @@ String.isub name2) name2 const_ocliskindof dot_iskindof id (\<lambda>_. []))"

end
