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

section\<open>Main Translation for: AsType\<close>

theory  Floor1_astype
imports Core_init
begin

definition "print_astype_consts = start_map O.consts o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts' (isub_name const_oclastype) (Typ_base (wrap_oclty name)) (const_mixfix dot_oclastype name))"

definition "print_astype_class = start_m' O.overloading
  (\<lambda> compare (isub_name, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
    Overloading'
          (isub_name const_oclastype)
          (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty h_name))))
          (S.flatten [isub_name const_oclastype, \<open>_\<close>, h_name])
          (let var_x = \<open>x\<close> in
           Term_rewrite
             (Term_postunary (Term_annot_ocl (Term_basic [var_x]) h_name) (Term_basic [dot_astype name]))
             \<open>\<equiv>\<close>
             (case compare
              of EQ \<Rightarrow>
                Term_basic [var_x]
              | x \<Rightarrow>
                Term_lam \<open>\<tau>\<close>
                  (\<lambda>var_tau. let val_invalid = Term_app \<open>invalid\<close> [Term_basic [var_tau]] in
                  Term_case
                    (Term_app var_x [Term_basic [var_tau]])
                    ( (Term_basic [\<open>\<bottom>\<close>], val_invalid)
                    # (Term_some (Term_basic [\<open>\<bottom>\<close>]), Term_app \<open>null\<close> [Term_basic [var_tau]])
                    # (let pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ String.isub h_name)
                              ; isub_name = (\<lambda>s. s @@ String.isub name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<open>_\<close>))
                              ; var_name = name in
                             Term_app (isub_h datatype_constr_name)
                                        ( Term_app (isub_n (isub_h datatype_ext_constr_name)) [Term_basic [var_name]]
                                        # l_extra) )
                         ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ String.isub name)
                              ; var_name = name in
                             Term_basic [var_name])
                         ; some_some = (\<lambda>x. Term_some (Term_some x)) in
                       if x = LT then
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name (L.map (\<lambda>_. Term_basic [\<open>None\<close>]) nl_attr))) ]
                       else
                         let l = [(Term_basic [wildcard], val_invalid)] in
                         if x = GT then
                           (some_some (pattern_complex h_name name (L.map (\<lambda>_. Term_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                           # l
                         else l) ) ))))"

definition "print_astype_from_universe =
 (let f_finish = (\<lambda> [] \<Rightarrow> ((id, Term_binop (Term_basic [\<open>Some\<close>]) \<open>o\<close>), [])
                  | _ \<Rightarrow> ((Term_some, id), [(Term_basic [wildcard], Term_basic [\<open>None\<close>])])) in
  start_m_gen O.definition
  (\<lambda> name l_inh _ l.
    let const_astype = print_astype_from_universe_name name in
    [ Definition (Term_rewrite (Term_basic [const_astype]) \<open>=\<close>
        (case f_finish l_inh of ((_, finish_with_some2), last_case_none) \<Rightarrow>
          finish_with_some2 (Term_function (L.flatten [l, last_case_none]))))])
  (\<lambda> l_inh _ _ compare (_, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
     if compare = UN' then [] else
     let ((finish_with_some1, _), _) = f_finish l_inh
       ; isub_h = (\<lambda> s. s @@ String.isub h_name)
       ; pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ String.isub h_name)
                              ; isub_name = (\<lambda>s. s @@ String.isub name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<open>_\<close>))
                              ; var_name = name in
                             Term_app (isub_h datatype_constr_name)
                                        ( Term_app (isub_n (isub_h datatype_ext_constr_name)) [Term_basic [var_name]]
                                        # l_extra ))
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ String.isub name)
                              ; var_name = name in
                             Term_basic [var_name])
       ; case_branch = (\<lambda>pat res. [(Term_app (isub_h datatype_in) [pat], finish_with_some1 res)]) in
             case compare
             of GT \<Rightarrow> case_branch (pattern_complex h_name name (L.map (\<lambda>_. Term_basic [wildcard]) hl_attr)) (pattern_simple name)
              | EQ \<Rightarrow> let n = Term_basic [name] in case_branch n n
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (L.map (\<lambda>_. Term_basic [\<open>None\<close>]) nl_attr))))"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
  [ Lemmas_simp \<open>\<close> (L.map (\<lambda>((isub_name, _), name).
    T.thm (S.flatten [isub_name const_oclastype, \<open>_\<close>, name])) name_set) ]))"

definition "print_astype_lemma_cp_set2 =
  (if activate_simp_optimization then
     \<lambda>expr base_attr.
       L.flatten (m_class' base_attr (\<lambda> compare (isub_name, name, _). \<lambda> OclClass name2 _ _ \<Rightarrow>
         if compare = EQ then
           []
         else
           [((isub_name, name), ((\<lambda>s. s @@ String.isub name2), name2))]) expr)
   else (\<lambda>_ _. []))"

definition "print_astype_lemmas_id2 = start_map'' id o (\<lambda>expr base_attr _ _.
  (let name_set = print_astype_lemma_cp_set2 expr base_attr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
  [ Lemmas_simp \<open>\<close> (L.map (\<lambda>((isub_name_h, _), (_, name)).
    T.thm (S.flatten [isub_name_h const_oclastype, \<open>_\<close>, name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map O.lemma o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma
      (S.flatten [\<open>cp_\<close>, const_oclastype, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      (let var_p = \<open>p\<close> in
       L.map
         (\<lambda>x. Term_app \<open>cp\<close> [x])
         [ Term_basic [var_p]
         , Term_lam \<open>x\<close>
             (\<lambda>var_x. Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_app var_p [Term_annot_ocl (Term_basic [var_x]) name3]) name2)
               (Term_basic [dot_astype name1])))])
      []
      (C.by [M.rule (T.thm \<open>cpI1\<close>), if check_opt name1 name2 then M.simp
                                             else M.simp_add [S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
  (\<lambda>expr. [Lemmas_simp \<open>\<close> (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      T.thm (S.flatten [\<open>cp_\<close>, const_oclastype, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (start_map O.lemma o
 get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma
      (S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Term_rewrite
             (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [name2]) name3)
               (Term_basic [dot_astype name1])))
             \<open>=\<close>
             (Term_basic [name2])]
      []
      (C.by (if check_opt name1 name3 then [M.simp]
                else [M.rule (T.thm \<open>ext\<close>)
                                      , M.simp_add (S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name3]
                                                      # hol_definition \<open>bot_option\<close>
                                                      # L.map hol_definition (if name2 = \<open>invalid\<close> then [\<open>invalid\<close>]
                                                         else [\<open>null_fun\<close>,\<open>null_option\<close>]))]))
  )) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x))) expr"

definition "print_astype_lemmas_strict = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
  (\<lambda>expr. [ Lemmas_simp \<open>\<close> (get_hierarchy_map (\<lambda>name1 name2 name3.
        T.thm (S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      ) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_defined = start_m O.lemma m_class_default
  (\<lambda> compare (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let var_X = \<open>X\<close>
       ; var_isdef = \<open>isdef\<close>
       ; f = \<lambda>e. Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Term_app \<open>\<delta>\<close> [e]) in
     case compare of LT \<Rightarrow>
        [ Lemma_assumes
          (S.flatten [isub_name const_oclastype, \<open>_\<close>, h_name, \<open>_defined\<close>])
          [(var_isdef, False, f (Term_basic [var_X]))]
          (f (Term_postunary (Term_annot_ocl (Term_basic [var_X]) h_name) (Term_basic [dot_astype name])))
          [C.using [T.thm var_isdef]]
          (C.by [M.auto_simp_add (S.flatten [isub_name const_oclastype, \<open>_\<close>, h_name]
                                        # \<open>foundation16\<close>
                                        # L.map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ])]) ]
      | _ \<Rightarrow> [])"

definition "print_astype_up_d_cast0_name name_any name_pers = S.flatten [\<open>up\<close>, String.isub name_any, \<open>_down\<close>, String.isub name_pers, \<open>_cast0\<close>]"
definition "print_astype_up_d_cast0 = start_map O.lemma o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (print_astype_up_d_cast0_name name_any name_pers)
        [(var_isdef, False, f (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
        (f (Term_binop
             (let asty = \<lambda>x ty. Term_warning_parenthesis (Term_postunary x (Term_basic [dot_astype ty])) in
              asty (asty (Term_annot_ocl (Term_basic [var_X]) name_pers) name_any) name_pers)
             \<open>\<triangleq>\<close> (Term_basic [var_X])))
        [C.using [T.thm var_isdef]]
        (C.by [M.auto_simp_add_split
                                    (L.map T.thm
                                    ( S.flatten [const_oclastype, String.isub name_any, \<open>_\<close>, name_pers]
                                    # S.flatten [const_oclastype, String.isub name_pers, \<open>_\<close>, name_any]
                                    # \<open>foundation22\<close>
                                    # \<open>foundation16\<close>
                                    # L.map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ]))
                                    (split_ty name_pers) ]))"

definition "print_astype_up_d_cast_name name_any name_pers = S.flatten [\<open>up\<close>, String.isub name_any, \<open>_down\<close>, String.isub name_pers, \<open>_cast\<close>]"
definition "print_astype_up_d_cast = start_map O.lemma o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_tau = \<open>\<tau>\<close> in
    Lemma_assumes
        (S.flatten [\<open>up\<close>, String.isub name_any, \<open>_down\<close>, String.isub name_pers, \<open>_cast\<close>])
        []
        (Term_binop
             (let asty = \<lambda>x ty. Term_warning_parenthesis (Term_postunary x (Term_basic [dot_astype ty])) in
              asty (asty (Term_annot_ocl (Term_basic [var_X]) name_pers) name_any) name_pers)
             \<open>=\<close> (Term_basic [var_X]))
        (L.map C.apply
          [[M.rule (T.thm \<open>ext\<close>), M.rename_tac [var_tau]]
          ,[M.rule (T.THEN (T.thm \<open>foundation22\<close>) (T.thm \<open>iffD1\<close>))]
          ,[M.case_tac (Term_binop (Term_basic [var_tau]) \<open>\<Turnstile>\<close>
              (Term_app \<open>\<delta>\<close> [Term_basic [var_X]])), M.simp_add [print_astype_up_d_cast0_name name_any name_pers]]
          ,[M.simp_add [\<open>defined_split\<close>], M.elim (T.thm \<open>disjE\<close>)]
          ,[M.plus [M.erule (T.thm \<open>StrongEq_L_subst2_rev\<close>), M.simp, M.simp]]])
        C.done)"

definition "print_astype_d_up_cast = start_map O.lemma o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_Y = \<open>Y\<close>
      ; a = \<lambda>f x. Term_app f [x]
      ; b = \<lambda>s. Term_basic [s]
      ; var_tau = \<open>\<tau>\<close>
      ; f_tau = \<lambda>s. Term_warning_parenthesis (Term_binop (b var_tau) \<open>\<Turnstile>\<close> (Term_warning_parenthesis s))
      ; var_def_X = \<open>def_X\<close>
      ; asty = \<lambda>x ty. Term_warning_parenthesis (Term_postunary x (Term_basic [dot_astype ty]))
      ; not_val = a \<open>not\<close> (a \<open>\<upsilon>\<close> (b var_X)) in
    Lemma_assumes
      (S.flatten [\<open>down\<close>, String.isub name_pers, \<open>_up\<close>, String.isub name_any, \<open>_cast\<close>])
      [(var_def_X, False, Term_binop
             (Term_basic [var_X])
             \<open>=\<close>
             (asty (Term_annot_ocl (Term_basic [var_Y]) name_pers) name_any))]
      (f_tau (Term_binop not_val \<open>or\<close>
               (Term_binop
                 (asty (asty (Term_basic [var_X]) name_pers) name_any)
                 \<open>\<doteq>\<close>
                 (b var_X))))
      (L.map C.apply
        [[M.case_tac (f_tau not_val), M.rule (T.thm \<open>foundation25\<close>), M.simp]])
      (C.by [ M.rule (T.thm \<open>foundation25'\<close>)
               , M.simp_add [ var_def_X
                              , print_astype_up_d_cast_name name_any name_pers
                              , \<open>StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym\<close>]]) )"

definition "print_astype_lemma_const expr = (start_map O.lemma o
  get_hierarchy_map
   (let a = \<lambda>f x. Term_app f [x]
      ; b = \<lambda>s. Term_basic [s]
      ; d = hol_definition
      ; check_opt =
          let set = print_astype_lemma_cp_set expr in
          (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set)
      ; var_X = \<open>X\<close> in
    (\<lambda>name1 name2 name3.
      let n = S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name3] in
      Lemma
        (S.flatten [n, \<open>_\<close>, name2])
        (L.map (a \<open>const\<close>)
          [ Term_annot' (b var_X) (wrap_oclty name3)
          , Term_postunary
                   (b var_X)
                   (Term_basic [dot_astype name1]) ])
        []
        (C.by [ M.simp_add [d \<open>const\<close>]
                 , M.option [M.metis0 [\<open>no_types\<close>] (L.map T.thm (n # \<open>prod.collapse\<close> # L.map d [\<open>bot_option\<close>, \<open>invalid\<close>, \<open>null_fun\<close>, \<open>null_option\<close>]))]])))
   (\<lambda>x. (x, [\<open>const\<close>], x))) expr"

definition "print_astype_lemmas_const = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
  (\<lambda>expr. [ Lemmas_simp \<open>\<close> (get_hierarchy_map (\<lambda>name1 name2 name3.
        T.thm (S.flatten [const_oclastype, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      ) (\<lambda>x. (x, [\<open>const\<close>], x)) expr)])
  else (\<lambda>_. []))"

end
