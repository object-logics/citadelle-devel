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

section\<open>Main Translation for: IsKindOf\<close>

theory  Floor1_iskindof
imports Core_init
begin

definition "print_iskindof_consts = start_map O.consts o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts' (isub_name const_ocliskindof) (Typ_base ty_boolean) (const_mixfix dot_ocliskindof name))"

definition "print_iskindof_class_name isub_name h_name = S.flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name]"
definition "print_iskindof_class = start_m_gen O.overloading m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    [ Overloading'
          (isub_name const_ocliskindof)
          (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty h_name))))
          (print_iskindof_class_name isub_name h_name)
          (let var_x = \<open>x\<close> in
           Term_rewrite
             (Term_postunary (Term_annot_ocl (Term_basic [var_x]) h_name) (Term_basic [dot_iskindof name]))
             \<open>\<equiv>\<close>
             (let isof = (\<lambda>f name. Term_warning_parenthesis (Term_postunary (Term_basic [var_x]) (Term_basic [f name]))) in
              term_binop \<open>or\<close> (isof dot_istypeof name # L.map (\<lambda> OclClass name_past _ _ \<Rightarrow> isof dot_iskindof name_past) next_dataty)))])"

definition "print_iskindof_from_universe = start_m O.definition
  (\<lambda>name _ _ l.
    let const_iskindof = S.flatten [const_ocliskindof, String.isub name, \<open>_\<AA>\<close>] in
    [ Definition (Term_rewrite (Term_basic [const_iskindof]) \<open>=\<close> (Term_function l)) ])
  (\<lambda> _ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    let isub_h = (\<lambda> s. s @@ String.isub h_name) in
    [ ( Term_app (isub_h datatype_in) [Term_basic [h_name]]
      , Term_warning_parenthesis
        (Term_postunary (Term_annot_ocl (Term_applys Term_basety [Term_basic [h_name]])
                                    h_name)
                        (Term_basic [dot_iskindof name])))])"

definition "print_iskindof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_iskindof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
  [ Lemmas_simp \<open>\<close> (L.map (\<lambda>((isub_name, _), name).
    T.thm (S.flatten [isub_name const_ocliskindof, \<open>_\<close>, name] )) name_set) ]))"

definition "print_iskindof_lemma_cp = start_m'3_gen O.lemma
 (\<lambda> _ _ next_dataty name1 name2 name3.
    let lemma_name = S.flatten [\<open>cp_\<close>, const_ocliskindof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2]
      ; lemma_spec = let var_p = \<open>p\<close> in
       L.map
         (\<lambda>x. Term_app \<open>cp\<close> [x])
         [ Term_basic [var_p]
         , Term_lam \<open>x\<close>
             (\<lambda>var_x. Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_app var_p [Term_annot_ocl (Term_basic [var_x]) name3]) name2)
               (Term_basic [dot_iskindof name1])))]
      ; lem_simp1 = M.simp_only [T.thm (S.flatten [const_ocliskindof, String.isub name1, \<open>_\<close>, name2])]
      ; lem_simp2 = M.simp_only [T.thm (S.flatten [\<open>cp_\<close>, const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])] in
    let (tac1, tac2) =
      if next_dataty = [] then ([], C.by [ lem_simp1 , lem_simp2 ])
      else
      ( [ [ lem_simp1 ]
        , [ M.plus
            [ M.rule (T.where (T.thm \<open>cpI2\<close>) [(\<open>f\<close>, Term_parenthesis (Term_basic [\<open>or\<close>]))])
            , M.plus [M.rule (T.thm \<open>allI\<close>)]
            , M.rule (T.thm \<open>cp_OclOr\<close>) ]]
        , [ lem_simp2 ] ]
      , C.by (L.map
            (\<lambda> OclClass n _ _ \<Rightarrow> M.simp_only [T.thm (S.flatten [\<open>cp_\<close>, const_ocliskindof, String.isub n, \<open>_\<close>, name3, \<open>_\<close>, name2])] )
            next_dataty))
    in Lemma lemma_name lemma_spec tac1 tac2)"

definition "print_iskindof_lemmas_cp = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
    (\<lambda>expr. [Lemmas_simp \<open>\<close>
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      T.thm (S.flatten [\<open>cp_\<close>, const_ocliskindof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict = start_m_gen O.lemma m_class_default
 (\<lambda> _ _ next_dataty _ (_, name1, _). \<lambda> OclClass name3 _ _ \<Rightarrow>
  L.map (\<lambda>(name2, name2').
    Lemma
      (S.flatten [const_ocliskindof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Term_rewrite
             (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [name2]) name3)
               (Term_basic [dot_iskindof name1])))
             \<open>=\<close>
             (Term_basic [name2'])]
      []
      (C.by
        (M.simp_only
           (L.map T.thm (L.flatten
              [ [S.flatten [const_ocliskindof, String.isub name1, \<open>_\<close>, name3]]
              , [S.flatten [const_oclistypeof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2]]
              , L.map
                  (\<lambda> OclClass n _ _ \<Rightarrow>
                    S.flatten [const_ocliskindof, String.isub n, \<open>_\<close>, name3, \<open>_\<close>, name2])
                  next_dataty ]))
        # (if next_dataty = [] then [] else [M.simp])) ))
    [(\<open>invalid\<close>,\<open>invalid\<close>),(\<open>null\<close>,\<open>true\<close>)])"

definition "print_iskindof_lemmas_strict = start_map'
 (if activate_simp_optimization then L.map O.lemmas o
  (\<lambda>expr. [ Lemmas_simp \<open>\<close> (get_hierarchy_map (\<lambda>name1 name2 name3.
      T.thm (S.flatten [const_ocliskindof, String.isub name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
  ) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_defined_name isub_name h_name = S.flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name, \<open>_defined\<close>]"
definition "print_iskindof_defined = start_m_gen O.lemma m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>symb e. Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Term_app symb [e]) in
      [ Lemma_assumes
          (print_iskindof_defined_name isub_name h_name)
          [(var_isdef, False, f \<open>\<upsilon>\<close> (Term_basic [var_X]))]
          (f \<open>\<delta>\<close> (Term_postunary (Term_annot_ocl (Term_basic [var_X]) h_name) (Term_basic [dot_iskindof name])))
          []
          (C.by [ M.simp_only [T.thm (S.flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name])]
                   , M.rule
                      (let mk_OF = \<lambda>f. T.OF (T.thm (f h_name)) (T.thm var_isdef) in
                       List.fold
                         (\<lambda> OclClass n _ _ \<Rightarrow> \<lambda> prf.
                           T.OF_l
                             (T.thm \<open>defined_or_I\<close>)
                             [ prf
                             , mk_OF (print_iskindof_defined_name (\<lambda>name. name @@ String.isub n))])
                         next_dataty
                         (mk_OF (print_istypeof_defined_name isub_name))) ])])"

definition "print_iskindof_defined'_name isub_name h_name = S.flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name, \<open>_defined'\<close>]"
definition "print_iskindof_defined' = start_m O.lemma m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>e. Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Term_app \<open>\<delta>\<close> [e]) in
      [ Lemma_assumes
          (print_iskindof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Term_basic [var_X]))]
          (f (Term_postunary (Term_annot_ocl (Term_basic [var_X]) h_name) (Term_basic [dot_iskindof name])))
          []
          (C.by [M.rule (T.OF (T.thm (print_iskindof_defined_name isub_name h_name))
                                     (T.THEN (T.thm var_isdef) (T.thm \<open>foundation20\<close>)))]) ])"

definition "print_iskindof_up_eq_asty = start_map O.lemma o map_class_gen_h'''''
  (\<lambda> _ name l_attr _ l_subtree next_dataty.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    [Lemma_assumes
        (print_iskindof_up_eq_asty_name name)
        [(var_isdef, False, f (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
        (f (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [var_X]) name)
               (Term_basic [dot_iskindof name]))))
        (L.map C.apply
        [ [ M.simp_only [T.thm (hol_definition \<open>OclValid\<close>)]
          , M.insert [T.thm var_isdef]]
        , L.flatten (fst (L.mapM
                      (\<lambda> OclClass n _ next \<Rightarrow> \<lambda>accu.
                        let (l_subst, accu) = L.mapM (\<lambda> _ (cpt, l_sub).
                          let l_sub = String.natural_to_digit10 cpt # l_sub in
                          ( M.subst_l
                              l_sub (* subst could fail without the list of integers *)
                              (T.thm \<open>cp_OclOr\<close>)
                          , Succ cpt
                          , l_sub)) next accu in
                        ( M.simp_only [T.thm (S.flatten [const_ocliskindof, String.isub n, \<open>_\<close>, name])]
                        # l_subst
                        , accu))
                      (OclClass name l_attr next_dataty # rev l_subtree) (1, [])))
        , [ M.auto_simp_add_split
              (let l = L.map T.thm (L.flatten ( [\<open>foundation16\<close>, hol_definition \<open>bot_option\<close>]
                                                     # L.map
                                                         (\<lambda> OclClass n _ _ \<Rightarrow> [S.flatten [const_oclistypeof, String.isub n, \<open>_\<close>, name]])
                                                         l_subtree)) in
               if l_subtree = [] then l else T.symmetric (T.thm \<open>cp_OclOr\<close>) # l)
              (\<open>option.split\<close> # L.flatten (split_ty name # L.map (\<lambda> OclClass n _ _ \<Rightarrow> split_ty n) l_subtree))]])
        (C.by [M.option [M.simp_all_add (L.map hol_definition [\<open>false\<close>, \<open>true\<close>, \<open>OclOr\<close>, \<open>OclAnd\<close>, \<open>OclNot\<close>])]])])"

definition "print_iskindof_up_larger = start_map O.lemma o
  map_class_nupl2''_inh (\<lambda>name_pers name_any name_pred.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close>
      ; disjI1 = \<open>foundation25\<close>
      ; disjI2 = \<open>foundation25'\<close> in
    Lemma_assumes
      (print_iskindof_up_larger_name name_pers name_any)
      [(var_isdef, False, f (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
      (f (Term_warning_parenthesis (Term_postunary
             (Term_annot_ocl (Term_basic [var_X]) name_pers)
             (Term_basic [dot_iskindof name_any]))))
      [C.apply [M.simp_only [T.thm (S.flatten [const_ocliskindof, String.isub name_any, \<open>_\<close>, name_pers])]] ]
      (C.by
        (case
            fst (List.fold (\<lambda> cl. \<lambda> (l, True) \<Rightarrow> (l, True)
                                  | (l, False) \<Rightarrow>
                                     let v =
                                       case cl of (OclClass n _ _, inh) \<Rightarrow>
                                         if n = name_pers then
                                           Some (print_iskindof_up_eq_asty_name name_pers)
                                         else if inh then
                                           Some (print_iskindof_up_larger_name name_pers n)
                                         else None in
                                     (v # l, v \<noteq> None))
              (rev (* priority of '_ or _' is right to left so we reverse *) name_pred)
              ([], False))
         of Some meth_last # l \<Rightarrow>
           L.map M.rule
             (L.flatten [ L.map (\<lambda>_. T.thm disjI1) l
                      , [ T.thm disjI2]
                      , [ T.OF (T.thm meth_last) (T.thm var_isdef)] ]))))"

datatype ('a, 'b) print_iskindof_up_istypeof_output
  = M_simp_only 'a
  | M_erule 'b
  | M_simp\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h\<^sub>_\<^sub>1 (* simp add: iskin *)
  | M_simp\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h\<^sub>_\<^sub>2
  | M_simp\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h

fun aux\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h
and aux\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h where
   "aux\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h =
     (\<lambda> [] \<Rightarrow> []
      | (class, l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h) # l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h \<Rightarrow>
         M_simp_only class
         # aux\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h class [] l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h (rev l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h))
      l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h"
 | "aux\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h class tactic l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h =
     (\<lambda> [] \<Rightarrow> tactic
      | (class0, class0_path_inh) # l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h \<Rightarrow>
         M_erule (class, class0 # map fst l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h)
         # (if l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h = [] then (#) M_simp\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h else id)
           (aux\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h
              class
              ( (if class0_path_inh then
                   (if l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h = [] then (#) M_simp\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h\<^sub>_\<^sub>1 else id)
                   (aux\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h)
                 else [M_simp\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h\<^sub>_\<^sub>2])
               @ tactic)
              l\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h
              l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h))
      l\<^sub>b\<^sub>r\<^sub>e\<^sub>a\<^sub>d\<^sub>t\<^sub>h"

definition "print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any =
 (let mk_OF = \<lambda>f. T.OF (T.thm (f name_any)) (T.thm var_isdef)
    ; next_dataty = case next_dataty of x # xs \<Rightarrow>
                      rev ((\<open>foundation26\<close>, x) # L.map (Pair \<open>defined_or_I\<close>) xs) in
  M.erule (List.fold
              (\<lambda> (rule_name, OclClass n _ _) \<Rightarrow> \<lambda> prf.
                T.OF_l
                  (T.thm rule_name)
                  [ prf
                  , mk_OF (print_iskindof_defined'_name (\<lambda>name. name @@ String.isub n))])
              next_dataty
              (mk_OF (print_istypeof_defined'_name (\<lambda>name. name @@ String.isub name_pers)))))"

definition "print_iskindof_up_istypeof_unfold_name name_pers name_any = S.flatten [\<open>not_\<close>, const_ocliskindof, String.isub name_pers, \<open>_then_\<close>, name_any, \<open>_\<close>, const_oclistypeof, \<open>_others_unfold\<close>]"
definition "print_iskindof_up_istypeof_unfold = start_m_gen O.lemma m_class_default
  (\<lambda> _ name_pred0 next_dataty compare (isub_name, name_pers, _). \<lambda> OclClass name_any _ _ \<Rightarrow>
  if compare = GT then
    let var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Term_parenthesis o Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    [ Lemma_assumes
        (print_iskindof_up_istypeof_unfold_name name_pers name_any)
        [(var_isdef, False, f id (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))
        ,(var_iskin, False, f id (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [var_X]) name_any)
                 (Term_basic [dot_iskindof name_pers]))))]
        (term_binop' \<open>\<or>\<close>
          (L.flatten
            (L.map (\<lambda>(f_dot, l). L.map
                 (\<lambda>name_pred. f id (Term_warning_parenthesis (Term_postunary
                   (Term_annot_ocl (Term_basic [var_X]) name_any)
                   (Term_basic [f_dot name_pred])))) l)
               [ (dot_istypeof, name_pers # L.map (\<lambda> OclClass n _ _ \<Rightarrow> n) name_pred0) ])))
        (C.using [T.thm var_iskin]
         # C.apply [M.simp_only [T.thm (S.flatten [isub_name const_ocliskindof, \<open>_\<close>, name_any])]]
         # (if next_dataty = [] then [] else L.flatten
              [ fst (L.mapM
                  (\<lambda>_ next_dataty.
                      ( C.apply [print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any]
                      , tl next_dataty))
                  next_dataty
                  (rev next_dataty))
              , [ C.apply [M.simp] ]
              , L.map (\<lambda> OclClass n _ _ \<Rightarrow>
                  C.apply [M.drule (T.OF (T.thm (print_iskindof_up_istypeof_unfold_name n name_any)) (T.thm var_isdef)), M.blast None]) next_dataty ]))
        C.done ]
  else [])"

definition "print_iskindof_up_istypeof_name name_pers name_any = S.flatten [\<open>not_\<close>, const_ocliskindof, String.isub name_pers, \<open>_then_\<close>, name_any, \<open>_\<close>, const_oclistypeof, \<open>_others\<close>]"
definition "print_iskindof_up_istypeof = start_map O.lemma o
  map_class_nupl2l'_inh (\<lambda>name_pers name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
      (print_iskindof_up_istypeof_name name_pers name_any)
      [(var_iskin, False, f (Term_preunary (Term_basic [\<open>\<not>\<close>])) (Term_warning_parenthesis (Term_postunary
             (Term_annot_ocl (Term_basic [var_X]) name_any)
               (Term_basic [dot_iskindof name_pers]))))
      ,(var_isdef, False, f id (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
      (term_binop' \<open>\<or>\<close>
        (L.flatten
          (L.map (\<lambda>(f_dot, l). L.map
               (\<lambda>name_pred. f id (Term_warning_parenthesis (Term_postunary
                 (Term_annot_ocl (Term_basic [var_X]) name_any)
                 (Term_basic [f_dot name_pred])))) l)
             [ (dot_istypeof, L.map (\<lambda> (name_pred, _). case Inh name_pred of OclClass n _ _ \<Rightarrow> n) name_pred0)
             , (dot_iskindof, L.flatten (L.map (\<lambda> (name_pred, _). case Inh_sib_unflat name_pred of l \<Rightarrow> L.map (\<lambda> OclClass n _ _ \<Rightarrow> n) l) name_pred0)) ])))
      (C.using [T.OF (T.thm (print_iskindof_up_eq_asty_name name_any)) (T.thm var_isdef)]
       # L.map (\<lambda>x. C.apply [x])
         (L.map
           (\<lambda> M_simp_only name_pred \<Rightarrow> M.simp_only [T.thm (print_iskindof_class_name (\<lambda>s. s @@ String.isub name_pred) name_any)]
            | M_erule (name_pred, next_dataty) \<Rightarrow>
                print_iskindof_up_istypeof_erule var_isdef next_dataty name_pred name_any
            | M_simp\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h\<^sub>_\<^sub>1 \<Rightarrow> M.simp_add [var_iskin]
            | _ \<Rightarrow> M.simp)
           (aux\<^sub>d\<^sub>e\<^sub>p\<^sub>t\<^sub>h (L.map (map_prod (\<lambda>class. case Inh class of OclClass class _ _ \<Rightarrow> class) id)
                           name_pred0))))
        C.done)"

definition "print_iskindof_up_d_cast = start_map O.lemma o
  map_class_nupl3'_LE'_inh (\<lambda>name_pers name_mid name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Term_binop (Term_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (S.flatten [\<open>down_cast_kind\<close>, String.isub name_mid, \<open>_from_\<close>, name_any, \<open>_to_\<close>, name_pers])
        [(var_iskin, False, f (Term_preunary (Term_basic [\<open>\<not>\<close>])) (Term_warning_parenthesis (Term_postunary
               (Term_annot_ocl (Term_basic [var_X]) name_any)
               (Term_basic [dot_iskindof name_mid]))))
        ,(var_isdef, False, f id (Term_app \<open>\<delta>\<close> [Term_basic [var_X]]))]
        (f id (Term_binop (Term_warning_parenthesis (Term_postunary
               (Term_basic [var_X])
               (Term_basic [dot_astype name_pers]))
             ) \<open>\<triangleq>\<close> (Term_basic [\<open>invalid\<close>])))
        (L.flatten
          (let name_pred_inh = L.map (\<lambda> (name_pred, _). Inh name_pred) name_pred0
             ; name_pred_inh_sib_gen = L.flatten (L.map (\<lambda> (name_pred, _). case Inh_sib name_pred of l \<Rightarrow> l) name_pred0)
             ; name_pred_inh_sib = L.map fst name_pred_inh_sib_gen
             ; f0 = \<lambda>name_pred. let name_pred = case name_pred of OclClass n _ _ \<Rightarrow> n in
                                [ M.rule (T.thm (print_istypeof_up_d_cast_name name_pred name_any name_pers))
                                , M.simp_only [] (* FIXME use wildcard *)
                                , M.simp_only [T.thm var_isdef]] in
           [ C.apply (  M.insert [T.OF_l (T.thm (print_iskindof_up_istypeof_name name_mid name_any)) (L.map T.thm [var_iskin, var_isdef])]
                  # (case L.flatten [ name_pred_inh, name_pred_inh_sib ]
                     of [] \<Rightarrow> [] | [_] \<Rightarrow> [] | _ \<Rightarrow> [ M.elim (T.thm \<open>disjE\<close>) ]))]
           # L.map (C.apply o f0) name_pred_inh
           # L.map (\<lambda> (OclClass name_pred l_attr next_d, l_subtree) \<Rightarrow>
                         L.map C.apply
                           [ [ M.drule (T.OF (T.thm (print_iskindof_up_istypeof_unfold_name name_pred name_any)) (T.thm var_isdef))]
                           , if next_d = [] then
                               f0 (OclClass name_pred l_attr next_d)
                             else
                               [ M.auto_simp_add
                                 (var_isdef # L.map
                                                (\<lambda> OclClass name_pred _ _ \<Rightarrow>
                                                  print_istypeof_up_d_cast_name name_pred name_any name_pers)
                                                l_subtree)] ])
                      name_pred_inh_sib_gen))
        C.done)"

end
