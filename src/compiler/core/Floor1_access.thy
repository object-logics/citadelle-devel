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

section\<open>Main Translation for: Accessor\<close>

theory  Floor1_access
imports Core_init
begin

definition "print_access_oid_uniq_gen Thy_def D_ocl_oid_start_upd def_rewrite =
  (\<lambda>expr env.
      (\<lambda>(l, oid_start). (L.map Thy_def l, D_ocl_oid_start_upd env oid_start))
      (let (l, (acc, _)) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = L.map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inh) in
         let (l, cpt) = L.mapM (L.mapM
           (\<lambda> (attr, OclTy_object (OclTyObj (OclTyCore ty_obj) _)) \<Rightarrow>
                                            (let obj_oid = TyObj_ass_id ty_obj
                                               ; obj_name_from_nat = TyObjN_ass_switch (TyObj_from ty_obj) in \<lambda>(cpt, rbt) \<Rightarrow>
             let (cpt_obj, cpt_rbt) =
               case RBT.lookup rbt obj_oid of
                 None \<Rightarrow> (cpt, oidSucAssoc cpt, RBT.insert obj_oid cpt rbt)
               | Some cpt_obj \<Rightarrow> (cpt_obj, cpt, rbt) in
             ( [def_rewrite obj_name_from_nat name isub_name attr (oidGetAssoc cpt_obj)]
             , cpt_rbt))
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (L.flatten (L.flatten l), cpt)) (D_ocl_oid_start env, RBT.empty) expr in
       (L.flatten l, acc)))"
definition "print_access_oid_uniq_ml =
  print_access_oid_uniq_gen
    O.ML
    (\<lambda>x _. x)
    (\<lambda>obj_name_from_nat name _ attr cpt_obj.
      SML (SML.rewrite_val
                   (SML.basic [print_access_oid_uniq_mlname obj_name_from_nat name attr])
                   \<open>=\<close>
                   (SML.oid \<open>\<close> cpt_obj)))"
definition "print_access_oid_uniq =
  print_access_oid_uniq_gen
    O.definition
    (\<lambda>env oid_start. env \<lparr> D_ocl_oid_start := oid_start \<rparr>)
    (\<lambda>obj_name_from_nat _ isub_name attr cpt_obj.
      Definition (Term_rewrite
                   (Term_basic [print_access_oid_uniq_name obj_name_from_nat isub_name attr])
                   \<open>=\<close>
                   (Term_oid \<open>\<close> cpt_obj)))"

definition "print_access_eval_extract _ = start_map O.definition
  (let lets = \<lambda>var def. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> def)
     ; a = \<lambda>f x. Term_app f [x]
     ; b = \<lambda>s. Term_basic [s] in
  [ let var_x = \<open>x\<close>
      ; var_f = \<open>f\<close>
      ; some_some = (\<lambda>x. Term_some (Term_some x))
      ; var_obj = \<open>obj\<close> in
    Definition (Term_rewrite
                  (Term_basic [var_eval_extract, var_x, var_f])
                  \<open>=\<close>
                  (Term_lam \<open>\<tau>\<close>
                     (\<lambda>var_tau. Term_case (Term_basic [var_x, var_tau])
                     [ (some_some (Term_basic [var_obj]), Term_app var_f [Term_app \<open>oid_of\<close> [Term_basic [var_obj]], Term_basic [var_tau]])
                     , (Term_basic [wildcard], Term_basic [\<open>invalid\<close>, var_tau])])))
  , lets var_in_pre_state (b \<open>fst\<close>)
  , lets var_in_post_state (b \<open>snd\<close>)
  , lets var_reconst_basetype Term_basety
  , let var_x = \<open>x\<close> in
     Definition (Term_rewrite (Term_basic [var_reconst_basetype_void, var_x])
                              \<open>=\<close>
                              (Term_binop (Term_basic [var_Abs_Void]) \<open>o\<close> (a var_reconst_basetype (b var_x)))) ])"


definition "print_access_choose_switch
              lets mk_var expr
              print_access_choose_n
              sexpr_list sexpr_function sexpr_pair =
  L.flatten
       (L.map
          (\<lambda>n.
           let l = L.upto 0 (n - 1) in
           L.map (let l = sexpr_list (L.map mk_var l) in (\<lambda>(i,j).
             (lets
                (print_access_choose_n n i j)
                (sexpr_function [(l, (sexpr_pair (mk_var i) (mk_var j)))]))))
             ((L.flatten o L.flatten) (L.map (\<lambda>i. L.map (\<lambda>j. if i = j then [] else [(i, j)]) l) l)))
          (class_arity expr))"
definition "print_access_choose_ml = start_map'''' O.ML o (\<lambda>expr _.
  (let b = \<lambda>s. SML.basic [s]
     ; lets = \<lambda>var exp. SML (SML.rewrite_val (SML.basic [var]) \<open>=\<close> exp)
     ; mk_var = \<lambda>i. b (S.flatten [\<open>x\<close>, String.natural_to_digit10 i]) in
   L.flatten
   [ print_access_choose_switch
       lets mk_var expr
       print_access_choose_mlname
       SML.list SML.function SML.pair ]))"
definition "print_access_choose = start_map'''' O.definition o (\<lambda>expr _.
  (let a = \<lambda>f x. Term_app f [x]
     ; b = \<lambda>s. Term_basic [s]
     ; lets = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> exp)
     ; lets' = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> (b exp))
     ; lets'' = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> (Term_lam \<open>l\<close> (\<lambda>var_l. Term_binop (b var_l) \<open>!\<close> (b exp))))
     ; _(* ignored *) =
        let l_flatten = \<open>L.flatten\<close> in
        [ lets l_flatten (let fun_foldl = \<lambda>f base.
                             Term_lam \<open>l\<close> (\<lambda>var_l. Term_app \<open>foldl\<close> [Term_lam \<open>acc\<close> f, base, a \<open>rev\<close> (b var_l)]) in
                           fun_foldl (\<lambda>var_acc.
                             fun_foldl (\<lambda>var_acc.
                               Term_lam \<open>l\<close> (\<lambda>var_l. Term_app \<open>Cons\<close> (L.map b [var_l, var_acc]))) (b var_acc)) (b \<open>Nil\<close>))
        , lets var_map_of_list (Term_app \<open>foldl\<close>
            [ Term_lam \<open>map\<close> (\<lambda>var_map.
                let var_x = \<open>x\<close>
                  ; var_l0 = \<open>l0\<close>
                  ; var_l1 = \<open>l1\<close>
                  ; f_map = a var_map in
                Term_lambdas0 (Term_pair (b var_x) (b var_l1))
                  (Term_case (f_map (b var_x))
                    (L.map (\<lambda>(pat, e). (pat, f_map (Term_binop (b var_x) \<open>\<mapsto>\<close> e)))
                      [ (b \<open>None\<close>, b var_l1)
                      , (Term_some (b var_l0), a l_flatten (Term_list (L.map b [var_l0, var_l1])))])))
            , b \<open>Map.empty\<close>])] in
  L.flatten
  [ let a = \<lambda>f x. Term_app f [x]
      ; b = \<lambda>s. Term_basic [s]
      ; lets = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> exp)
      ; mk_var = \<lambda>i. b (S.flatten [\<open>x\<close>, String.natural_to_digit10 i]) in
    print_access_choose_switch
      lets mk_var expr
      print_access_choose_name
      Term_list Term_function Term_pair
  , [ let var_pre_post = \<open>pre_post\<close>
        ; var_to_from = \<open>to_from\<close>
        ; var_assoc_oid = \<open>assoc_oid\<close>
        ; var_f = \<open>f\<close>
        ; var_oid = \<open>oid\<close> in
      Definition (Term_rewrite
        (Term_basic [var_deref_assocs, var_pre_post, var_to_from, var_assoc_oid, var_f, var_oid ])
        \<open>=\<close>
        (Term_lam
           \<open>\<tau>\<close>
           (\<lambda>var_tau.
           Term_case (Term_app var_assocs [Term_app var_pre_post [Term_basic [var_tau]]
                                                                      ,Term_basic [var_assoc_oid]])
             [ let var_S = \<open>S\<close> in
               ( Term_some (Term_basic [var_S])
               , Term_app var_f
                   [ Term_app var_deref_assocs_list (L.map b [var_to_from, var_oid, var_S])
                   , Term_basic [var_tau]])
             , (Term_basic[wildcard], Term_app \<open>invalid\<close> [Term_basic [var_tau]]) ]))) ]] ))"

definition "print_access_deref_oid_name isub_name = isub_name var_deref_oid"
definition "print_access_deref_oid = start_map O.definition o
  map_class (\<lambda>isub_name _ _ _ _ _.
    let var_fs = \<open>fst_snd\<close>
      ; var_f = \<open>f\<close>
      ; var_oid = \<open>oid\<close>
      ; var_obj = \<open>obj\<close> in
    Definition (Term_rewrite
                  (Term_basic [print_access_deref_oid_name isub_name, var_fs, var_f, var_oid])
                  \<open>=\<close>
                  (Term_lam \<open>\<tau>\<close>
                     (\<lambda>var_tau. Term_case (Term_app \<open>heap\<close> [Term_basic [var_fs, var_tau], Term_basic [var_oid]])
                     [ (Term_some (Term_basic [isub_name datatype_in, var_obj]), Term_basic [var_f, var_obj, var_tau])
                     , (Term_basic [wildcard], Term_basic [\<open>invalid\<close>, var_tau]) ]))))"

definition "print_access_deref_assocs_name' name_from isub_name isup_attr =
  S.flatten [var_deref, \<open>_\<close>, isub_name var_assocs, \<open>_\<close>, String.natural_to_digit10 name_from, isup_attr \<open>_\<close>]"
definition "print_access_deref_assocs_name name_from isub_name attr =
  print_access_deref_assocs_name' name_from isub_name (\<lambda>s. s @@ String.isup attr)"
definition "print_access_deref_assocs = start_map'''' O.definition o (\<lambda>expr design_analysis.
  (if design_analysis = Gen_only_design then \<lambda>_. [] else (\<lambda>expr. L.flatten (L.flatten (map_class (\<lambda>isub_name name l_attr l_inherited _ _.
  let l_inherited = map_class_inh l_inherited in
  let var_fst_snd = \<open>fst_snd\<close>
    ; var_f = \<open>f\<close>
    ; b = \<lambda>s. Term_basic [s] in
    L.flatten (L.map (L.map
      (\<lambda> (attr, OclTy_object (OclTyObj (OclTyCore ty_obj) _)) \<Rightarrow>
           let name_from = TyObjN_ass_switch (TyObj_from ty_obj) in
           [Definition (Term_rewrite
                  (Term_basic [print_access_deref_assocs_name name_from isub_name attr, var_fst_snd, var_f])
                  \<open>=\<close>
                  (Term_binop
                    (Term_app
                      var_deref_assocs
                        (L.map b [ var_fst_snd
                               , print_access_choose_name (TyObj_ass_arity ty_obj) name_from (TyObjN_ass_switch (TyObj_to ty_obj))
                               , print_access_oid_uniq_name name_from isub_name attr
                               , var_f ]))
                    \<open>\<circ>\<close>
                    (b \<open>oid_of\<close>)))]
       | _ \<Rightarrow> []))
      (l_attr # l_inherited))) expr)))) expr)"

definition "print_access_select_name isup_attr isub_name = isup_attr (isub_name var_select)"
definition "print_access_select = start_map'' O.definition o (\<lambda>expr base_attr _ base_attr''.
  let b = \<lambda>s. Term_basic [s] in
  map_class_arg_only0 (\<lambda>isub_name name l_attr.
    let l_attr = base_attr l_attr in
    let var_f = \<open>f\<close>
      ; wildc = Term_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ String.isup attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Term_rewrite
                       (Term_basic [print_access_select_name isup_attr isub_name, var_f])
                       \<open>=\<close>
                       (let var_attr = b (\<open>x_\<close> @@ String.isup attr) in
                        Term_function
                          (L.map (\<lambda>(lhs,rhs). ( Term_app
                                                         (isub_name datatype_constr_name)
                                                         ( wildc
                                                         # L.flatten [l_wildl, [lhs], l_wildr])
                                                     , rhs))
                            [ ( Term_basic [\<open>\<bottom>\<close>], Term_basic [\<open>null\<close>] )
                            , ( Term_some var_attr
                              , Term_app var_f [var_attr]) ]))) # l_acc))
      ([], L.map (\<lambda>_. wildc) (tl l_attr), [])
      l_attr) in
    rev l)
  (\<lambda>isub_name name (l_attr, l_inherited, l_cons).
    let l_inherited = L.flatten (L.map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inherited)) in
    let (l_attr, l_inherited) = base_attr'' (l_attr, l_inherited) in
    let var_f = \<open>f\<close>
      ; wildc = Term_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ String.isup attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Term_rewrite
                       (Term_basic [isup_attr (isub_name var_select), var_f])
                       \<open>=\<close>
                       (let var_attr = b (\<open>x_\<close> @@ String.isup attr) in
                        Term_function
                          (L.flatten (L.map (\<lambda>(lhs,rhs). ( Term_app
                                                         (isub_name datatype_constr_name)
                                                         ( Term_app (isub_name datatype_ext_constr_name)
                                                             (wildc # L.flatten [l_wildl, [lhs], l_wildr])
                                                         # L.map (\<lambda>_. wildc) l_attr)
                                                     , rhs))
                            [ ( Term_basic [\<open>\<bottom>\<close>], Term_basic [\<open>null\<close>] )
                            , ( Term_some var_attr
                              , Term_app var_f [var_attr]) ]
                            # (L.map (\<lambda> OclClass x _ _ \<Rightarrow> let var_x = String.lowercase x in
                                             (Term_app
                                                         (isub_name datatype_constr_name)
                                                         ( Term_app (datatype_ext_constr_name @@ mk_constr_name name x)
                                                             [Term_basic [var_x]]
                                                         # L.map (\<lambda>_. wildc) l_attr), (Term_app (isup_attr (var_select @@ String.isub x))
                                                                                                     (L.map (\<lambda>x. Term_basic [x]) [var_f, var_x]) ))) (of_sub l_cons))
                            # [])))) # l_acc))
      ([], L.map (\<lambda>_. wildc) (tl l_inherited), [])
      l_inherited) in
    rev l) expr)"

definition "print_access_select_obj_name' isub_name attr = isub_name var_select @@ attr"
definition "print_access_select_obj_name isub_name attr = print_access_select_obj_name' isub_name (String.isup attr)"
definition "print_access_select_obj = start_map'''' O.definition o (\<lambda>expr design_analysis.
  (if design_analysis = Gen_only_design then \<lambda>_. [] else (\<lambda>expr. L.flatten (L.flatten (map_class (\<lambda>isub_name name l_attr l_inh _ _.
    let l_inh = map_class_inh l_inh in
    L.flatten (fst (L.mapM (L.mapM
      (\<lambda> (attr, OclTy_object (OclTyObj (OclTyCore ty_obj) _)) \<Rightarrow> \<lambda>rbt.
          if lookup2 rbt (name, attr) = None then
           ( [ Definition
                (let b = \<lambda>s. Term_basic [s] in
                 Term_rewrite
                  (b (isub_name var_select @@ String.isup attr))
                  \<open>=\<close>
                  (b (let obj_mult = TyObjN_role_multip (TyObj_to ty_obj) in
                      case (is_sequence obj_mult, single_multip obj_mult) of
                        (True, True) \<Rightarrow> var_select_object_sequence_any
                      | (True, False) \<Rightarrow> var_select_object_sequence
                      | (False, True) \<Rightarrow> var_select_object_set_any
                      | (False, False) \<Rightarrow> var_select_object_set)))]
           , insert2 (name, attr) () rbt)
         else ([], rbt)
       | _ \<Rightarrow> Pair []))
      (l_attr # l_inh) RBT.empty))) expr)))) expr)"

definition "print_access_dot_consts =
 (L.mapM (\<lambda>(f_update, x) env. (O.consts x, env \<lparr> D_ocl_accessor := f_update (D_ocl_accessor env) \<rparr> ))) o
  (L.flatten o L.flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    L.map (\<lambda>(attr_n, attr_ty).
      L.map
        (\<lambda>(var_at_when_hol, var_at_when_ocl, f_update_ocl).
          let name =
             S.flatten [ \<open>dot\<close>
                     , case attr_ty of
                         OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow> S.flatten [\<open>_\<close>, String.natural_to_digit10 (TyObjN_ass_switch (TyObj_from ty_obj)), \<open>_\<close>]
                       | _ \<Rightarrow> \<open>\<close>
                     , String.isup attr_n, var_at_when_hol] in
          ( f_update_ocl (\<lambda> l. String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name # l)
          , Consts_raw0
            name
            (Ty_arrow
              (Typ_apply (Typ_base \<open>val\<close>) [Typ_base \<open>\<AA>\<close>, Typ_base \<open>'\<alpha>\<close>])
              (print_access_dot_consts_ty attr_ty))
            (let dot_name = mk_dot attr_n var_at_when_ocl
               ; mk_par = \<lambda>s1 s2. S.flatten [s1, \<open> '/* \<close>, s2, \<open> *'/\<close>] in
             case attr_ty of OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
               (case apply_optim_ass_arity
                       ty_obj
                       (mk_par
                          dot_name
                          (let ty_obj = TyObj_from ty_obj in
                           case TyObjN_role_name ty_obj of
                                None => String.natural_to_digit10 (TyObjN_ass_switch ty_obj)
                              | Some s => s)) of
                  None \<Rightarrow> dot_name
                | Some dot_name \<Rightarrow> dot_name)
                           | _ \<Rightarrow> dot_name)
            None))
        [ (var_at_when_hol_post, var_at_when_ocl_post, update_D_ocl_accessor_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre, update_D_ocl_accessor_pre)]) l_attr))"

definition "print_access_dot_name isub_name dot_at_when attr_ty isup_attr =
  S.flatten [ isup_attr (let dot_name = isub_name \<open>dot\<close> in
                       case attr_ty of
                         OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow> S.flatten [dot_name, \<open>_\<close>, String.natural_to_digit10 (TyObjN_ass_switch (TyObj_from ty_obj)), \<open>_\<close>]
                       | _ \<Rightarrow> dot_name)
          , dot_at_when]"

fun print_access_dot_aux where
   "print_access_dot_aux deref_oid x =
    (\<lambda> OclTy_collection c ty \<Rightarrow>
         Term_app (if is_sequence c then var_select_object_sequence else var_select_object_set)
                    [print_access_dot_aux deref_oid ty]
     | OclTy_pair ty1 ty2 \<Rightarrow> Term_app var_select_object_pair [print_access_dot_aux deref_oid ty1, print_access_dot_aux deref_oid ty2]
     | OclTy_object (OclTyObj (OclTyCore_pre s) _) \<Rightarrow> deref_oid (Some s) [Term_basic [var_reconst_basetype]]
     | OclTy_base_void \<Rightarrow> Term_basic [var_reconst_basetype_void]
     | _ \<Rightarrow> Term_basic [var_reconst_basetype]) x"

definition "print_access_dot = start_map'''' O.overloading o (\<lambda>expr design_analysis.
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
            let overloading_name = print_access_dot_name id dot_at_when attr_ty isup_attr in
            [ Overloading
                overloading_name
                (Term_annot (Term_basic [overloading_name]) (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty name)))))
                (print_access_dot_name isub_name dot_at_when attr_ty isup_attr)
                (let var_x = \<open>x\<close> in
                 Term_rewrite
                   (dot_attr (Term_annot_ocl (Term_basic [var_x]) name))
                   \<open>\<equiv>\<close>
                   (Term_app var_eval_extract [Term_basic [var_x],
                    let deref_oid = \<lambda>attr_orig l. Term_app (case attr_orig of None \<Rightarrow> isub_name var_deref_oid
                                                                              | Some orig_n \<Rightarrow> var_deref_oid @@ String.isub orig_n) (Term_basic [var_in_when_state] # l) in
                    deref_oid None
                      [ ( case attr_ty of
                            OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
                              if design_analysis = Gen_only_design then id else
                                (\<lambda>l. Term_app (print_access_deref_assocs_name' (TyObjN_ass_switch (TyObj_from ty_obj)) isub_name isup_attr) (Term_basic [var_in_when_state] # [l]))
                          | _ \<Rightarrow> id)
                          (Term_app (isup_attr (isub_name var_select))
                            [case attr_ty of
                               OclTy_raw _ \<Rightarrow> Term_basic [var_reconst_basetype]
                             | OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
                                 let ty_obj = TyObj_to ty_obj
                                   ; der_name = deref_oid (Some (TyObjN_role_ty ty_obj)) [Term_basic [var_reconst_basetype]] in
                                 if design_analysis = Gen_only_design then
                                   let obj_mult = TyObjN_role_multip ty_obj
                                     ; (var_select_object_name_any, var_select_object_name) =
                                         if is_sequence obj_mult then
                                           (var_select_object_sequence_any, var_select_object_sequence)
                                         else
                                           (var_select_object_set_any, var_select_object_set) in
                                   Term_app (if single_multip obj_mult then
                                                 var_select_object_name_any
                                               else
                                                 var_select_object_name) [der_name]
                                 else
                                   der_name
                             | x \<Rightarrow> print_access_dot_aux deref_oid x ]) ] ])) ]) expr)"

definition "print_access_dot_lemmas_id_set =
  (if activate_simp_optimization then
     map_class_arg_only_var'
       (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _. [print_access_dot_name isub_name dot_at_when attr_ty isup_attr])
   else (\<lambda>_. []))"

definition "print_access_dot_lemmas_id_name = \<open>dot_accessor\<close>"
definition "print_access_dot_lemmas_id = start_map' (\<lambda>expr.
       (let name_set = print_access_dot_lemmas_id_set expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> L.map O.lemmas
         [ Lemmas_nosimp print_access_dot_lemmas_id_name (L.map T.thm name_set) ]))"

definition "print_access_dot_cp_lemmas_set =
  (if activate_simp_optimization then [hol_definition var_eval_extract] else [])"

definition "print_access_dot_cp_lemmas = start_map' (\<lambda>_.
  L.map (\<lambda>x. O.lemmas (Lemmas_simp \<open>\<close> [T.thm x])) print_access_dot_cp_lemmas_set)"

definition "print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr = S.flatten [\<open>cp_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr]"
definition "print_access_dot_lemma_cp = start_map O.lemma o
 (let auto = \<lambda>l. M.auto_simp_add2 [T.thms print_access_dot_lemmas_id_name] (L.map hol_definition (\<open>cp\<close> # l)) in
  map_class_arg_only_var
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Term_app \<open>cp\<close> [Term_lam \<open>X\<close> (\<lambda>var_x. dot_attr (Term_annot_ocl (Term_basic [var_x]) name)) ]]
                []
                (C.by [auto (if print_access_dot_cp_lemmas_set = [] then
                                  [var_eval_extract, S.flatten [isup_attr (isub_name \<open>dot\<close>), dot_at_when]]
                                else
                                  [])]) ])
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Term_app \<open>cp\<close> [Term_lam \<open>X\<close> (\<lambda>var_x. dot_attr (Term_annot_ocl (Term_basic [var_x]) name)) ]]
                []
                (if print_access_dot_cp_lemmas_set = [] then C.sorry (* fold l_hierarchy, take only subclass, unfold the corresponding definition *)
                 else C.by [auto []]) ]))"

definition "print_access_dot_lemmas_cp = start_map O.lemmas o (\<lambda>expr.
  case map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _.
      [T.thm (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr) ])
    expr
  of [] \<Rightarrow> []
   | l \<Rightarrow> [Lemmas_simp \<open>\<close> l])"

definition "print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr name_invalid = S.flatten [print_access_dot_name isub_name dot_at_when attr_ty isup_attr, \<open>_\<close>, name_invalid]"
definition "print_access_lemma_strict expr = (start_map O.lemma o
  map_class_arg_only_var' (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            L.map (\<lambda>(name_invalid, meth_invalid). Lemma
                  (print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr name_invalid)
                  [Term_rewrite
                     (dot_attr (Term_annot_ocl (Term_basic [name_invalid]) name))
                     \<open>=\<close>
                     (Term_basic [\<open>invalid\<close>])]
                  []
                  (if print_access_dot_lemmas_id_set expr = [] | print_access_dot_cp_lemmas_set = [] then
                     C.sorry else
                   C.by [ M.rule (T.thm \<open>ext\<close>),
                             M.simp_add2 [T.thms print_access_dot_lemmas_id_name]
                                           (L.map hol_definition
                                             (let l = (let l = (\<open>bot_option\<close> # meth_invalid) in
                                              if print_access_dot_lemmas_id_set expr = [] then
                                                S.flatten [isup_attr (isub_name \<open>dot\<close>), dot_at_when] # l
                                              else l) in
                                              if print_access_dot_cp_lemmas_set = []
                                              then
                                                \<open>eval_extract\<close> # l
                                              else l))]) )
                [(\<open>invalid\<close>, [\<open>invalid\<close>]), (\<open>null\<close>, [\<open>null_fun\<close>, \<open>null_option\<close>])])) expr"

definition "print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr =
  S.flatten [ \<open>defined_mono_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr ]"
definition "print_access_def_mono = start_map'''' O.lemma o (\<lambda>expr _.
  map_class_arg_only_var'
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
      let var_X = \<open>X\<close>
        ; var_tau = \<open>\<tau>\<close>
        ; a = \<lambda>f x. Term_app f [x]
        ; b = \<lambda>s. Term_basic [s]
        ; f0 = \<lambda>e. Term_binop (Term_basic [var_tau]) \<open>\<Turnstile>\<close> e
        ; f = \<lambda>e. f0 (Term_app \<open>\<delta>\<close> [e]) in
            [ Lemma
                (print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr)
                (L.map f [ dot_attr (Term_annot_ocl (b var_X) name)
                            , b var_X ])
                (let f_tac = \<lambda>s.
                   [ M.case_tac (f0 (Term_warning_parenthesis (Term_rewrite (b var_X) \<open>\<triangleq>\<close> (b s))))
                   , M.insert [T.where (T.thm \<open>StrongEq_L_subst2\<close>)
                                           [ (\<open>P\<close>, Term_lam \<open>x\<close> (\<lambda>var_X. a \<open>\<delta>\<close> (dot_attr (b var_X))))
                                           , (\<open>\<tau>\<close>, b \<open>\<tau>\<close>)
                                           , (\<open>x\<close>, b var_X)
                                           , (\<open>y\<close>, b s)]]
                   , M.simp_add [ \<open>foundation16'\<close>
                                  , print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr s] ] in
                 [ f_tac \<open>invalid\<close>
                 , f_tac \<open>null\<close> ])
                (C.by [M.simp_add [\<open>defined_split\<close>]]) ]) expr)"

definition "print_access_is_repr_name isub_name dot_at_when attr_ty isup_attr =
  S.flatten [ \<open>is_repr_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr ]"
definition "print_access_is_repr = start_map'''' O.lemma o (\<lambda>expr design_analysis.
 (let is_design = design_analysis = Gen_only_design
    ; App_a = \<lambda>l. C.apply (if is_design then [] else l)
    ; App_d = \<lambda>l. C.apply (if is_design then l else []) in
  (if is_design then
     (* TODO extend the support to object inherited attributes *)
     map_class_arg_only_var''
   else
     map_class_arg_only_var')
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
      case attr_ty of OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
     (let ty_mult = TyObjN_role_multip (TyObj_to ty_obj) in
      if single_multip ty_mult then
      let var_X = \<open>X\<close>
        ; var_tau = \<open>\<tau>\<close>
        ; var_def_dot = \<open>def_dot\<close>
        ; a = \<lambda>f x. Term_app f [x]
        ; ap = \<lambda>f x. Term_applys (Term_pat f) [x]
        ; ap' = \<lambda>f x. Term_applys (Term_pat f) x
        ; b = \<lambda>s. Term_basic [s]
        ; f0 = \<lambda>e. Term_binop (Term_basic [var_tau]) \<open>\<Turnstile>\<close> e
        ; f = \<lambda>e. f0 (Term_app \<open>\<delta>\<close> [e])
        ; attr_ty' = is_sequence ty_mult
        ; name_from = TyObjN_ass_switch (TyObj_from ty_obj)
        ; name_to = TyObjN_role_ty (TyObj_to ty_obj)
        ; isub_name_to = \<lambda>s. s @@ String.isub name_to in
            [ Lemma_assumes
                (print_access_is_repr_name isub_name dot_at_when attr_ty isup_attr)
                [ (var_def_dot, False, f (dot_attr (Term_annot_ocl (b var_X) name))) ]
                (Term_app \<open>is_represented_in_state\<close> [b var_in_when_state, dot_attr (Term_basic [var_X]), b name_to, b var_tau])
(let (* existential variables *)
     v_a0 = \<open>a0\<close>
   ; v_a = \<open>a\<close>
   ; v_b = \<open>b\<close>
   ; v_r = \<open>r\<close>
   ; v_typeoid = \<open>typeoid\<close>
   ; v_opt = \<open>opt\<close>
   ; v_aa = \<open>aa\<close>
   ; v_e = \<open>e\<close>
   ; v_aaa = \<open>aaa\<close>

     (* schematic variables *)
   ; vs_t = \<open>t\<close>
   ; vs_sel_any = \<open>sel_any\<close>

     (* *)
   ; l_thes = \<lambda>l l_when. Some (l @@@@ [Term_pat \<open>thesis\<close>], l_when)
   ; l_thes0 = \<lambda>l l_when. Some (l @@@@ [Term_pat \<open>t\<close>], l_when)
   ; hol_d = L.map hol_definition
   ; thol_d = L.map (T.thm o hol_definition)
   ; App_f = \<lambda>l e. C.fix_let l [] e []
   ; App_d_f = \<lambda>l e. if is_design then App_f l e else C.apply []
   ; App_f' = \<lambda>l. C.fix_let l []
   ; f_ss = \<lambda>v. a \<open>Some\<close> (a \<open>Some\<close> (b v))
   ; insert_that = M.insert [T.thms \<open>that\<close>] in
 [ C.apply [M.insert [T.simplified (T.OF (T.thm (print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr))
                                           (T.thm var_def_dot))
                                   (T.thm \<open>foundation16\<close>)]]
 , C.apply [M.case_tac (a var_X (b var_tau)), M.simp_add [hol_definition \<open>bot_option\<close>]]
 (* *)
 , App_f' [v_a0]
          (l_thes [Term_binop (a var_X (b var_tau)) \<open>=\<close> (a \<open>Some\<close> (b v_a0))]
                  [Term_binop (a var_X (b var_tau)) \<open>\<noteq>\<close> (b \<open>null\<close>)])
          [C.apply_end [M.simp_all]]
 , C.apply [insert_that, M.case_tac (b v_a0), M.simp_add (L.map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close>]), M.clarify]
 (* *)
 , App_f [v_a] (l_thes [ Term_binop (a var_X (b var_tau)) \<open>=\<close> (f_ss v_a) ] [])
 , C.apply [M.case_tac (Term_app \<open>heap\<close> [ a var_in_when_state (b var_tau)
                                          , a \<open>oid_of\<close> (b v_a)]), M.simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>])]
 , C.apply [ M.insert [T.thm \<open>def_dot\<close>]
       , M.simp_add_split ( T.thm (print_access_dot_name isub_name dot_at_when attr_ty isup_attr)
                            # thol_d [ \<open>is_represented_in_state\<close>
                                     , print_access_select_name isup_attr isub_name
                                     , print_access_deref_oid_name isub_name
                                     , var_in_when_state
                                     , \<open>defined\<close>, \<open>OclValid\<close>, \<open>false\<close>, \<open>true\<close>, \<open>invalid\<close>, \<open>bot_fun\<close>])
                            [T.thm \<open>if_split_asm\<close>]]
 (* *)
 , App_f [v_b] (l_thes [ Term_binop (a var_X (b var_tau)) \<open>=\<close> (f_ss v_a)
                       , Term_rewrite (Term_app \<open>heap\<close> [ a var_in_when_state (b var_tau)
                                                           , a \<open>oid_of\<close> (b v_a)])
                                      \<open>=\<close>
                                      (a \<open>Some\<close> (b v_b)) ]
                       [])
 , C.apply [ M.insert [T.simplified (T.thm \<open>def_dot\<close>) (T.thm \<open>foundation16\<close>)]
       , M.auto_simp_add ( print_access_dot_name isub_name dot_at_when attr_ty isup_attr
                           # hol_d [ \<open>is_represented_in_state\<close>
                                   , print_access_deref_oid_name isub_name
                                   , \<open>bot_option\<close>, \<open>null_option\<close>])]
 , C.apply [ M.case_tac (b v_b), M.simp_all_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>]) ]
 , App_a [ M.simp_add (hol_d [print_access_deref_assocs_name' name_from isub_name isup_attr, var_deref_assocs]) ]
 , App_a [ M.case_tac (Term_app (\<open>assocs\<close>) [ a var_in_when_state (b var_tau)
                                               , b (print_access_oid_uniq_name' name_from isub_name (isup_attr \<open>\<close>)) ])
         , M.simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>])
         , M.simp_add (hol_d [print_access_select_obj_name' isub_name (isup_attr \<open>\<close>)]) ]
 (* *)
 , C.fix_let
     [v_r, v_typeoid]
     [ ( Term_pat vs_t
       , Term_rewrite (f_ss v_r) \<open>\<in>\<close> (Term_binop
                                              (Term_parenthesis
                                                (Term_binop (b \<open>Some\<close>) \<open>o\<close> (b (print_astype_from_universe_name name_to))))
                                              \<open>`\<close>
                                              (a \<open>ran\<close> (a \<open>heap\<close> (a var_in_when_state (b var_tau))))))
     , ( Term_pat vs_sel_any
       , Term_app (if attr_ty' then var_select_object_sequence_any else var_select_object_set_any)
                    [ Term_app (print_access_deref_oid_name isub_name_to) [b var_in_when_state, b var_reconst_basetype] ])]
     (Some ( [ Term_rewrite (if is_design then
                               Term_app (print_access_select_name isup_attr isub_name)
                                        [ Term_pat vs_sel_any
                                        , b v_typeoid
                                        , b var_tau ]
                             else
                               Term_applys (Term_pat vs_sel_any)
                                        [ b v_typeoid
                                        , b var_tau ]) \<open>=\<close> (f_ss v_r)
             , Term_pat vs_t ]
           , []))
     []
 , App_d [ M.case_tac (b v_typeoid), M.simp_add (hol_d [print_access_select_name isup_attr isub_name]) ]
 (* *)
 , App_d_f [v_opt]
     (l_thes0
       [ Term_rewrite (Term_applys (Term_case (b v_opt)
                                              [ (b \<open>None\<close>, b \<open>null\<close>)
                                              , let var_x = \<open>x\<close> in
                                                (a \<open>Some\<close> (b var_x), ap vs_sel_any (b var_x)) ])
                                   [ b var_tau ])
                      \<open>=\<close>
                      (f_ss v_r) ]
       [])
 , App_d [ M.case_tac (b v_opt), M.auto_simp_add (hol_d [\<open>null_fun\<close>, \<open>null_option\<close>, \<open>bot_option\<close>]) ]
 (* *)
 , App_f' [v_aa]
     (l_thes0
       [Term_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ]) \<open>=\<close> (f_ss v_r)]
       [Term_binop (b var_tau) \<open>\<Turnstile>\<close> (a \<open>\<delta>\<close> (ap vs_sel_any (b v_aa)))])
     [ C.apply_end [ M.simp_add (\<open>foundation16\<close> # hol_d [\<open>bot_option\<close>, \<open>null_option\<close>]) ] ]
 , C.apply [ insert_that
           , M.drule (T.simplified (T.thm (if attr_ty' then
                                               var_select_object_sequence_any_exec
                                             else
                                               var_select_object_set_any_exec))
                                   (T.thm \<open>foundation22\<close>)), M.erule (T.thm \<open>exE\<close>) ]
 (* *)
 , App_f' [v_e]
     (l_thes0
       []
       [ Term_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ]) \<open>=\<close> (f_ss v_r)
       , Term_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ])
                      \<open>=\<close>
                      (Term_app (print_access_deref_oid_name isub_name_to)
                                  (L.map b [ var_in_when_state
                                              , var_reconst_basetype
                                              , v_e
                                              , var_tau ])) ])
     [ C.apply_end [ M.plus [M.blast None] ] ]
 , C.apply [ insert_that, M.simp_add (hol_d [print_access_deref_oid_name isub_name_to]) ]
 , C.apply [ M.case_tac (Term_app \<open>heap\<close> [ a var_in_when_state (b var_tau), b v_e ])
       , M.simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>]), M.simp ]
 (* *)
 , App_f [v_aaa]
     (l_thes0
       [ Term_rewrite (Term_case (b v_aaa)
                                 [ let var_obj = \<open>obj\<close> in
                                   (a (isub_name_to datatype_in) (b var_obj), Term_app var_reconst_basetype [b var_obj, b var_tau])
                                 , (b wildcard, a \<open>invalid\<close> (b var_tau)) ])
                      \<open>=\<close>
                      (f_ss v_r)
       , Term_rewrite (Term_app \<open>heap\<close> [ a var_in_when_state (b var_tau), b v_e ])
                      \<open>=\<close>
                      (a \<open>Some\<close> (b v_aaa)) ]
       [])
 , C.apply [ M.case_tac (b v_aaa), M.auto_simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>, \<open>image\<close>, \<open>ran\<close>]) ]
 , C.apply [ M.rule (T.where (T.thm \<open>exI\<close>) [(\<open>x\<close>, a (isub_name_to datatype_in) (b v_r))])
       , M.simp_add_split (thol_d [print_astype_from_universe_name name_to, \<open>Let\<close>, var_reconst_basetype])
                            [T.thm \<open>if_split_asm\<close>] ] ])
                (C.by [ M.rule' ]) ] else [] (* TODO *))
      | _ \<Rightarrow> [] (* TODO *))) expr)"

definition "print_access_repr_allinst = start_map''''' O.lemma o (\<lambda>expr (sorry, dirty) design_analysis.
  if sorry = Some Gen_sorry | sorry = None & dirty then
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
      case attr_ty of OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow>
        let var_tau = \<open>\<tau>\<close>
          ; f = \<lambda>e. Term_binop (Term_basic [var_tau]) \<open>\<Turnstile>\<close> e
          ; a = \<lambda>f x. Term_app f [x]
          ; b = \<lambda>s. Term_basic [s]
          ; var_x = \<open>x\<close> in
            [ Lemma
                (S.flatten [ isup_attr (S.flatten [isub_name \<open>dot_repr\<close>, \<open>_\<close>, String.natural_to_digit10 (TyObjN_ass_switch (TyObj_from ty_obj)), \<open>_\<close>])
                         , dot_at_when])
                ([ f (a \<open>\<delta>\<close> (dot_attr (Term_annot_ocl (Term_basic [var_x]) name)))
                 , let all_inst = if var_in_when_state \<triangleq> var_in_pre_state then
                                        \<open>OclAllInstances_at_pre\<close>
                                      else
                                        \<open>OclAllInstances_at_post\<close> in
                   Term_binop
                      (let ty_obj = TyObj_to ty_obj
                         ; name' = TyObjN_role_ty ty_obj
                         ; obj_mult = TyObjN_role_multip ty_obj in
                       f (Term_app
                            (if single_multip obj_mult then
                               \<open>UML_Set.OclIncludes\<close>
                             else
                               \<open>UML_Set.OclIncludesAll\<close>)
                            [ a all_inst (b name')
                            , let x = dot_attr (b var_x) in
                              if is_sequence obj_mult then
                                a \<open>OclAsSet\<^sub>S\<^sub>e\<^sub>q\<close> x
                              else
                                x ]))
                      \<open>\<and>\<close>
                      (f (Term_app \<open>UML_Set.OclIncludes\<close> [ a all_inst (b name)
                                                           , b var_x ]))])
                []
                C.sorry ]
      | _ \<Rightarrow> []) expr
  else [])"

end
