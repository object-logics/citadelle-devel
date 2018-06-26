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

section\<open>Main Translation for: IsTypeOf\<close>

theory  Floor1_istypeof
imports Core_init
begin

definition "print_istypeof_consts = start_map O.consts o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts' (isub_name const_oclistypeof) (Typ_base ty_boolean) (const_mixfix dot_oclistypeof name))"

definition "print_istypeof_class = start_m_gen O.overloading m_class_default
  (\<lambda> l_inh _ _ compare (isub_name, name, _). \<lambda> OclClass h_name hl_attr h_last \<Rightarrow>
   [Overloading'
          (isub_name const_oclistypeof)
          (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty h_name))))
          (S.flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name])
          (let var_x = \<open>x\<close> in
           Term_rewrite
             (Term_postunary (Term_annot_ocl (Term_basic [var_x]) h_name) (Term_basic [dot_istypeof name]))
             \<open>\<equiv>\<close>
             (Term_lam \<open>\<tau>\<close>
                  (\<lambda>var_tau. let app_tau = (\<lambda>v. Term_app v [Term_basic [var_tau]]) in
                  Term_case
                    (app_tau var_x)
                    ( (Term_basic [\<open>\<bottom>\<close>], app_tau \<open>invalid\<close>)
                    # (Term_some (Term_basic [\<open>\<bottom>\<close>]), app_tau \<open>true\<close>)
                    # (let l_false = [(Term_basic [wildcard], app_tau \<open>false\<close>)]
                         ; pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ String.isub h_name) in
                             (Term_some (Term_some
                               (Term_app (isub_h datatype_constr_name)
                                           ( Term_app (f2 (\<lambda>s. isub_name (s @@ \<open>_\<close>)) (isub_h datatype_ext_constr_name))
                                                        (Term_basic [wildcard] # f1)
                                           # L.map (\<lambda>_. Term_basic [wildcard]) hl_attr))), app_tau \<open>true\<close>)
                             # (if h_last = [] then [] else l_false)) in
                       case compare
                       of EQ \<Rightarrow> pattern_complex_gen (L.flatten (L.map (L.map (\<lambda>_. Term_basic [wildcard]) o (\<lambda> OclClass _ l _ \<Rightarrow> l)) (of_linh l_inh))) (\<lambda>_. id)
                        | GT \<Rightarrow> pattern_complex_gen [] id
                        | _ \<Rightarrow> l_false) ) )))] )"

definition "print_istypeof_from_universe = start_m O.definition
  (\<lambda> name _ _ l.
    let const_istypeof = S.flatten [const_oclistypeof, String.isub name, \<open>_\<AA>\<close>] in
    [ Definition (Term_rewrite (Term_basic [const_istypeof]) \<open>=\<close> (Term_function l))])
  (\<lambda>_ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let isub_h = (\<lambda> s. s @@ String.isub h_name) in
     [( Term_app (isub_h datatype_in) [Term_basic [h_name]]
      , Term_warning_parenthesis
        (Term_postunary (Term_annot_ocl (Term_applys Term_basety [Term_basic [h_name]])
                                    h_name)
                        (Term_basic [dot_istypeof name])))])"

definition "print_istypeof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_istypeof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
  [ Lemmas_simp \<open>\<close> (L.map (\<lambda>((isub_name, _), name).
    T.thm (S.flatten [isub_name const_oclistypeof, \<open>_\<close>, name] )) name_set) ]))"

definition "print_istypeof_lemma_cp expr = (start_map O.lemma o
  (get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma
      (S.flatten [\<open>cp_\<close>, const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      (let var_p = \<open>p\<close> in
       L.map
         (\<lambda>x. Term_app \<open>cp\<close> [x])
         [ Term_basic [var_p]
         , Term_lam \<open>x\<close>
             (\<lambda>var_x. Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_app var_p [Term_annot_ocl (Term_basic [var_x]) name3]) name2)
               (Term_basic [dot_istypeof name1])))])
      []
      (C.by [M.rule (T.thm \<open>cpI1\<close>), if check_opt name1 name2 then M.simp
                                             else M.simp_add [S.flatten [const_oclistypeof, String.isub name1, \<open>_\<close>, name2]]])
  )) (\<lambda>x. (x, x, x))) ) expr"

definition "print_istypeof_lemmas_cp = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
    (\<lambda>expr. [Lemmas_simp \<open>\<close>
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      T.thm (S.flatten [\<open>cp_\<close>, const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
   (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_istypeof_lemma_strict expr = (start_map O.lemma o
  get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 (name2,name2') name3.
    Lemma
      (S.flatten [const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Term_rewrite
             (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [name2]) name3)
               (Term_basic [dot_istypeof name1])))
             \<open>=\<close>
             (Term_basic [name2'])]
      []
      (C.by (let l = L.map hol_definition (\<open>bot_option\<close> # (if name2 = \<open>invalid\<close> then [\<open>invalid\<close>]
                                                              else [\<open>null_fun\<close>,\<open>null_option\<close>])) in
                [M.rule (T.thm \<open>ext\<close>), M.simp_add (if check_opt name1 name3 then l
                                                           else S.flatten [const_oclistypeof, String.isub name1, \<open>_\<close>, name3] # l)]))
  )) (\<lambda>x. (x, [(\<open>invalid\<close>,\<open>invalid\<close>),(\<open>null\<close>,\<open>true\<close>)], x))) expr"

definition "print_istypeof_lemmas_strict_set =
  (if activate_simp_optimization then
    get_hierarchy_map (\<lambda>name1 name2 name3. (name1, name3, name2)) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_strict expr = start_map O.lemmas
  (case print_istypeof_lemmas_strict_set expr
   of [] \<Rightarrow> []
    | l \<Rightarrow> [ Lemmas_simp \<open>\<close> (L.map
      (\<lambda>(name1, name3, name2).
        T.thm (S.flatten [const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
      l) ])"

definition "print_istypeof_defined = start_m O.lemma m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>symb e. Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Term_app symb [e]) in
      [ Lemma_assumes
          (print_istypeof_defined_name isub_name h_name)
          [(var_isdef, False, f \<open>\<upsilon>\<close> (Term_basic [var_X]))]
          (f \<open>\<delta>\<close> (Term_postunary (Term_annot_ocl (Term_basic [var_X]) h_name) (Term_basic [dot_istypeof name])))
          [C.apply [M.insert [T.simplified (T.thm var_isdef) (T.thm \<open>foundation18'\<close>) ]
               ,M.simp_only [T.thm (hol_definition \<open>OclValid\<close>)]
               ,M.subst (T.thm \<open>cp_defined\<close>)]]
          (C.by [M.auto_simp_add_split ( T.symmetric (T.thm \<open>cp_defined\<close>)
                                            # L.map T.thm ( hol_definition \<open>bot_option\<close>
                                                          # [ S.flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name] ]))
                                            (\<open>option.split\<close> # split_ty h_name) ]) ])"

definition "print_istypeof_defined' = start_m O.lemma m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>e. Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Term_app \<open>\<delta>\<close> [e]) in
      [ Lemma_assumes
          (print_istypeof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Term_basic [var_X]))]
          (f (Term_postunary (Term_annot_ocl (Term_basic [var_X]) h_name) (Term_basic [dot_istypeof name])))
          []
          (C.by [M.rule (T.OF (T.thm (print_istypeof_defined_name isub_name h_name))
                                     (T.THEN (T.thm var_isdef) (T.thm \<open>foundation20\<close>)))]) ])"

definition "print_istypeof_up_larger_name name_pers name_any = S.flatten [\<open>actualType\<close>, String.isub name_pers, \<open>_larger_staticType\<close>, String.isub name_any]"
definition "print_istypeof_up_larger = start_map O.lemma o
  map_class_nupl2'_inh_large (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (print_istypeof_up_larger_name name_pers name_any)
        [(var_isdef, False, f (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
        (f (Term_binop (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [var_X]) name_pers)
               (Term_basic [dot_istypeof name_any]))
             ) \<open>\<triangleq>\<close> (Term_basic [\<open>false\<close>])))
        [C.using [T.thm var_isdef]]
        (C.by [M.auto_simp_add ( S.flatten [const_oclistypeof, String.isub name_any, \<open>_\<close>, name_pers]
                                    # \<open>foundation22\<close>
                                    # \<open>foundation16\<close>
                                    # L.map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ])]))"

definition "print_istypeof_up_d_cast expr = (start_map O.lemma o
  map_class_nupl3'_GE_inh (\<lambda>name_pers name_mid name_any.
    let var_X = \<open>X\<close>
      ; var_istyp = \<open>istyp\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (print_istypeof_up_d_cast_name name_mid name_any name_pers)
        [(var_istyp, False, f (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [var_X]) name_any)
               (Term_basic [dot_istypeof name_mid]))))
        ,(var_isdef, False, f (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
        (f (Term_binop (Term_warning_parenthesis (Term_postunary
               (Term_basic [var_X])
               (Term_basic [dot_astype name_pers]))
             ) \<open>\<triangleq>\<close> (Term_basic [\<open>invalid\<close>])))
        [C.using (L.map T.thm [var_istyp, var_isdef])
        ,C.apply [M.auto_simp_add_split (L.map T.thm
                                      ( S.flatten [const_oclastype, String.isub name_pers, \<open>_\<close>, name_any]
                                      # \<open>foundation22\<close>
                                      # \<open>foundation16\<close>
                                      # L.map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ]))
                                      (split_ty name_any) ]]
        (C.by [M.simp_add (let l = L.map hol_definition [\<open>OclValid\<close>, \<open>false\<close>, \<open>true\<close>] in
                                if name_mid = name_any & ~(print_istypeof_lemma_cp_set expr = []) then
                                  l
                                else
                                  S.flatten [const_oclistypeof, String.isub name_mid, \<open>_\<close>, name_any] # l)]))) expr"

end
