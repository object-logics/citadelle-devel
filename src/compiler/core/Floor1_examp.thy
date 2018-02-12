(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Floor1_examp.thy ---
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

section\<open>Main Translation for: Example (Floor 1)\<close>

theory  Floor1_examp
imports Core_init
begin

definition "print_examp_oclbase_gen =
 (\<lambda> OclDefInteger nb \<Rightarrow>
        let name = var_OclInteger @@ nb
          ; b = \<lambda>s. Term_basic [s]
          ; ab_name = b nb in
        (ab_name, Definition_where2
          name
          (b (String.to_bold_number nb))
          (Term_rewrite (b name) \<open>=\<close> (Term_lambda wildcard (Term_some (Term_some ab_name)))))
  | OclDefReal (nb0, nb1) \<Rightarrow>
        let name = S.flatten [ var_OclReal, nb0, \<open>_\<close>, nb1 ]
          ; b = \<lambda>s. Term_basic [s]
          ; ab_name = b (S.flatten [nb0(*(* WARNING
                                          uncomment this as soon as OCL_basic_type_Real.thy
                                          is not implemented as 'nat' *), \<open>.\<close>, nb1*)]) in
        (ab_name, Definition_where2
          name
          (b (S.flatten [String.to_bold_number nb0, \<open>.\<close>, String.to_bold_number nb1]))
          (Term_rewrite (b name) \<open>=\<close> (Term_lambda wildcard (Term_some (Term_some ab_name)))))
  | OclDefString nb \<Rightarrow>
        let name = var_OclString @@ String.base255 nb
          ; b = \<lambda>s. Term_basic [s] in
        if \<not> String.is_empty nb & String.all is_letter nb then
          let ab_name = b (S.flatten [\<open>''\<close>, nb, \<open>''\<close>]) in
          (ab_name,
          Definition_where2 name (b (text2_of_str nb))
            (Term_rewrite (b name) \<open>=\<close> (Term_lambda wildcard (Term_some (Term_some ab_name)))))
        else
          let ab_name = b (text_of_str nb) in
          (ab_name,
          Definition
            (Term_rewrite (b name) \<open>=\<close> (Term_lambda wildcard (Term_some (Term_some ab_name))))))"

definition "print_examp_oclbase = (\<lambda> OclDefBase l \<Rightarrow> (start_map O.definition o L.map (snd o print_examp_oclbase_gen)) l)"

datatype print_examp_instance_draw_list_attr = Return_obj ocl_ty_class
                                             | Return_exp semi__term
datatype print_examp_instance_draw_list_attr_err = Return_err_ty "ocl_ty \<times> ocl_data_shallow"
                                                 | Return_err_ty_auto (* automated type reconstruction failed *)
                                                 | Return_ocl_null
                                                 | Return_ocl_invalid
                                                 | Return_object_variable string
                                                 | Return_err_l "print_examp_instance_draw_list_attr_err list"
datatype 'a print_examp_instance_draw_list_attr' = Return_val 'a
                                                 | Return_err print_examp_instance_draw_list_attr_err

definition "bind\<^sub>e\<^sub>r\<^sub>r v f = (case v of Return_val x \<Rightarrow> f x
                                  | Return_err x \<Rightarrow> Return_err x)"

definition "map\<^sub>e\<^sub>r\<^sub>r f v = bind\<^sub>e\<^sub>r\<^sub>r v (Return_val o f)"

fun fold\<^sub>e\<^sub>r\<^sub>r where
   "fold\<^sub>e\<^sub>r\<^sub>r f e accu = (\<lambda> Return_err_ty _ \<Rightarrow> f e accu
                       | Return_err_ty_auto \<Rightarrow> f e accu
                       | Return_ocl_invalid \<Rightarrow> f e accu
                       | Return_err_l l \<Rightarrow> List.fold (fold\<^sub>e\<^sub>r\<^sub>r f) l accu
                       | _ \<Rightarrow> accu) e"

fun has_err_ty where
   "has_err_ty e = (\<lambda> Return_err_ty _ \<Rightarrow> True
                    | Return_err_ty_auto \<Rightarrow> True
                    | Return_err_l l \<Rightarrow> list_ex has_err_ty l
                    | _ \<Rightarrow> False) e"

fun has_invalid where
   "has_invalid e = (\<lambda> Return_ocl_invalid \<Rightarrow> True
                     | Return_err_l l \<Rightarrow> list_ex has_invalid l
                     | _ \<Rightarrow> False) e"

definition "list_bind\<^sub>e\<^sub>r\<^sub>r f0 f l =
 (case List.partition (\<lambda> Return_err _ \<Rightarrow> True | _ \<Rightarrow> False) (L.map f0 l) of
    ([], l) \<Rightarrow> Return_val (f (L.map (\<lambda> Return_val e \<Rightarrow> e) l))
  | (l, _) \<Rightarrow> Return_err (Return_err_l (L.map (\<lambda> Return_err e \<Rightarrow> e) l)))"

definition "filter_ocl_exn s v =
     (if s \<triangleq> \<open>null\<close> then
        Return_err Return_ocl_null
      else if s \<triangleq> \<open>invalid\<close> then
        Return_err Return_ocl_invalid
      else
        v)"

definition "print_examp_instance_draw_list_attr_aux_base =
 (\<lambda> (_, ShallB_term t) \<Rightarrow>
      Return_val (fst (print_examp_oclbase_gen t)) (* some typing errors are not returned here but some could be raised later, since further checks will occur when evaluating meta embedded commands *)
  | (ty, ShallB_str s) \<Rightarrow> filter_ocl_exn s (Return_err (Return_err_ty (ty, ShallB_str s)))
  | e \<Rightarrow> Return_err (Return_err_ty e))"

fun print_examp_instance_draw_list_attr_aux where
   "print_examp_instance_draw_list_attr_aux f_oid_rec e =
    (\<lambda>
     (* object case 2 *)
       (OclTy_collection _ ty, ShallB_list l) \<Rightarrow>
         list_bind\<^sub>e\<^sub>r\<^sub>r (\<lambda>e. print_examp_instance_draw_list_attr_aux f_oid_rec (ty, e)) Term_list l
     | (OclTy_pair ty1 ty2, ShallB_list [e1, e2]) \<Rightarrow>
         list_bind\<^sub>e\<^sub>r\<^sub>r id
                    (\<lambda> [e1, e2] \<Rightarrow> Term_pair e1 e2)
                    [ print_examp_instance_draw_list_attr_aux f_oid_rec (ty1, e1)
                    , print_examp_instance_draw_list_attr_aux f_oid_rec (ty2, e2) ]
     | (OclTy_object (OclTyObj (OclTyCore_pre _) _), shall) \<Rightarrow> f_oid_rec e
     (* base cases *)
     | (OclTy_base_integer, _) \<Rightarrow> print_examp_instance_draw_list_attr_aux_base e
     | (OclTy_base_real, _) \<Rightarrow> print_examp_instance_draw_list_attr_aux_base e
     | (OclTy_base_string, _) \<Rightarrow> print_examp_instance_draw_list_attr_aux_base e
     | (OclTy_class_syn _, _) \<Rightarrow> print_examp_instance_draw_list_attr_aux_base e
     (* enum case *)
     | (OclTy_enum _, ShallB_str s) \<Rightarrow> filter_ocl_exn s (Return_val (Term_basic [pref_constr_enum s]))
     (* type error *)
     | e \<Rightarrow> Return_err (Return_err_ty e)) e"

definition "print_examp_instance_draw_list_attr = (\<lambda>(f_oid, f_oid_rec).
  let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; filter_ty_err = \<lambda>pre_post f.
             \<lambda> Return_val v \<Rightarrow> Return_val (f v)
             | Return_err err \<Rightarrow> if has_err_ty err | has_invalid err then
                                   Return_err err
                                 else
                                   case (pre_post, err) of (Some (pre, post), Return_object_variable s) \<Rightarrow>
                                                             Return_val (a \<open>Some\<close> (a \<open>oid_of\<close> (Term_app s [Term_pair (b pre) (b post)])))
                                                         | _ \<Rightarrow> Return_val (b \<open>None\<close>) in
  list_bind\<^sub>e\<^sub>r\<^sub>r
   (\<lambda> obj.
    bind\<^sub>e\<^sub>r\<^sub>r
     ( case obj of
         (t_obj, None) \<Rightarrow> Return_val (case t_obj of Some ty_obj \<Rightarrow> Return_obj ty_obj
                                                  | _ \<Rightarrow> Return_exp (b \<open>None\<close>))
       (* object case 1 *)
       | (_, Some (OclTy_object (OclTyObj (OclTyCore ty_obj) _), _)) \<Rightarrow> Return_val (Return_obj ty_obj)
       (* *)
       | (_, Some (ty, pre_post, shallow)) \<Rightarrow>
         map\<^sub>e\<^sub>r\<^sub>r Return_exp (filter_ty_err pre_post Term_some (print_examp_instance_draw_list_attr_aux f_oid_rec (ty, shallow))))
     (\<lambda> Return_obj ty_obj \<Rightarrow> filter_ty_err None id (f_oid ty_obj)
      | Return_exp exp \<Rightarrow> Return_val exp))
   id)"

definition "print_examp_instance_app_constr_notmp f_oid = (\<lambda>isub_name app_x l_attr.
  map\<^sub>e\<^sub>r\<^sub>r
    (\<lambda>l. Term_app (isub_name datatype_constr_name) (app_x # l))
    (print_examp_instance_draw_list_attr f_oid l_attr))"

definition "rbt_of_class env =
  (let rbt = (snd o fold_class_gen (\<lambda>_ name l_attr l_inh _ _ rbt.
     ( [()]
     , modify_def (RBT.empty, []) name
         (let f_fold = \<lambda>tag l rbt.
            let (rbt, _, n) = List.fold
                                   (\<lambda> (name_attr, ty) \<Rightarrow> \<lambda>(rbt, cpt, l_obj).
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Succ cpt, (case ty of OclTy_object (OclTyObj (OclTyCore ty_obj) _) \<Rightarrow> Some ty_obj | _ \<Rightarrow> None) # l_obj))
                                   l
                                   (rbt, 0, []) in
            (rbt, (tag, n)) in
          (\<lambda>(rbt, _).
           let (rbt, info_own) = f_fold OptOwn l_attr rbt in
           let (rbt, info_inh) = f_fold OptInh (L.flatten (map_class_inh l_inh)) rbt in
           (rbt, [info_own, info_inh])))
         rbt)) RBT.empty) (case D_input_class env of Some c \<Rightarrow> c) in
   (\<lambda>name.
     let rbt = lookup rbt name in
     ( rbt = None
     , \<lambda> name_attr.
        Option.bind rbt (\<lambda>(rbt, _). lookup rbt name_attr)
     , \<lambda> v. Option.bind rbt (\<lambda>(_, l).
        map_option (\<lambda>l f accu.
          let (_, accu) =
            List.fold
              (let f_fold = \<lambda>b (n, accu). (Succ n, f b n accu) in
               if D_ocl_semantics env = Gen_only_design then
                 f_fold
               else
                 \<lambda> Some _ \<Rightarrow> (\<lambda>(n, accu). (Succ n, accu))
                 | None \<Rightarrow> f_fold None) (rev l) (0, accu) in
          accu) (L.assoc v l)))))"

definition "fill_blank f_blank =
  L.map (\<lambda> (attr_ty, l).
    case f_blank attr_ty of Some f_fold \<Rightarrow>
    let rbt = List.fold (\<lambda> ((ty, _, ident), shallow) \<Rightarrow> RBT.insert ident (ty, shallow)) l RBT.empty in
    (attr_ty, rev (f_fold (\<lambda>b n l. (b, RBT.lookup rbt (OptIdent n)) # l) [])))"

fun split_inh_own where
   "split_inh_own f_class s_cast l_attr =
  (let (f_attr, f_blank) = f_class s_cast
     ; split = \<lambda>l. List.partition (\<lambda>((_, OptOwn, _), _) \<Rightarrow> True | _ \<Rightarrow> False)
                                  (List.map_filter (\<lambda>(pre_post, name_attr, data). map_option (\<lambda>x. (x, (pre_post, data))) (f_attr name_attr)) l) in
   case l_attr of
     OclAttrNoCast l \<Rightarrow>
       let (l_own, l_inh) = split l in
       OclAttrNoCast (fill_blank f_blank [(OptOwn, l_own), (OptInh, l_inh)])
   | OclAttrCast s_cast l_attr l \<Rightarrow>
       case split l of (l_own, []) \<Rightarrow>
       OclAttrCast s_cast (split_inh_own f_class s_cast l_attr) (fill_blank f_blank [(OptOwn, l_own)]))"

fun print_examp_instance_app_constr2_notmp where
   "print_examp_instance_app_constr2_notmp l_attr isub_name cpt f_oid =
 (case l_attr of
    OclAttrNoCast [(OptOwn, l_own), (OptInh, l_inh)] \<Rightarrow>
    bind\<^sub>e\<^sub>r\<^sub>r
      (map\<^sub>e\<^sub>r\<^sub>r
        (let var_oid = Term_oid var_oid_uniq (oidGetInh cpt) in
         (\<lambda>l. (Term_app (isub_name datatype_ext_constr_name) (var_oid # l), l_own)))
        (print_examp_instance_draw_list_attr (f_oid isub_name cpt) l_inh))
      (\<lambda>(l_inh, l_own).
        print_examp_instance_app_constr_notmp (f_oid isub_name cpt) isub_name l_inh l_own)
  | OclAttrCast x l_attr _ \<Rightarrow>
    print_examp_instance_app_constr2_notmp l_attr (\<lambda>s. s @@ String.isub x) cpt f_oid)"

fun print_examp_instance_app_constr2_notmp' where
   "print_examp_instance_app_constr2_notmp' l_attr e =
 (case l_attr of
    OclAttrNoCast _ \<Rightarrow> e (* NOTE: to be enclosed in a potentially not mandatory parenthesis *)
  | OclAttrCast ty (OclAttrNoCast _) _ \<Rightarrow> Term_annot' e (wrap_oclty ty) (* NOTE: to be enclosed in a mandatory parenthesis *)
  | OclAttrCast ty l_attr _ \<Rightarrow>
      Term_postunary (Term_parenthesis (print_examp_instance_app_constr2_notmp' l_attr e)) (Term_basic [dot_astype ty]))"

definition "inst_name ocli = (case Inst_name ocli of Some n \<Rightarrow> n)"

definition "init_map_class env l =
  (let (rbt_nat, rbt_str, _, _) =
     List.fold
       (\<lambda> ocli (rbt_nat, rbt_str, oid_start, accu).
         let f = \<lambda>_.
             ( RBT.insert (Oid accu) oid_start rbt_nat
             , insert (inst_name ocli) oid_start rbt_str
             , oidSucInh oid_start
             , Succ accu) in
         case Inst_attr_with ocli of
           None \<Rightarrow> f ()
         | Some s \<Rightarrow>
             (case lookup rbt_str s of None \<Rightarrow> f ()
              | Some oid_start' \<Rightarrow>
                ( RBT.insert (Oid accu) oid_start' rbt_nat
                , insert (inst_name ocli) oid_start' rbt_str
                , oid_start
                , Succ accu)))
       l
       ( RBT.empty
       , RBT.bulkload (L.map (\<lambda>(k, _, v). (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list k, v)) (D_input_instance env))
       , D_ocl_oid_start env
       , 0) in
   (rbt_of_class env, RBT.lookup rbt_nat, lookup rbt_str))"

definition "print_examp_def_st_assoc_build_rbt_gen f rbt map_self map_username l_assoc =
  List.fold
     (\<lambda> (ocli, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         f ty
         (List.fold (\<lambda>(_, name_attr, shall).
           case f_attr_ty name_attr of
             Some (OclTy_object (OclTyObj (OclTyCore ty_obj) _), _, _) \<Rightarrow>
               modify_def ([], ty_obj) name_attr
               (\<lambda>(l, accu). case let find_map = \<lambda> ShallB_str s \<Rightarrow> map_username s | ShallB_self s \<Rightarrow> map_self s | _ \<Rightarrow> None in
                                 case shall of
                                   ShallB_list l \<Rightarrow> if list_ex (\<lambda>x. find_map x = None) l then
                                                      None
                                                    else
                                                      Some (List.map_filter find_map l)
                                 | _ \<Rightarrow> map_option (\<lambda>x. [x]) (find_map shall) of
                      None \<Rightarrow> (l, accu)
                    | Some oid \<Rightarrow> (L.map (L.map oidGetInh) [[cpt], oid] # l, accu))
           | _ \<Rightarrow> id) l_attr)) ocli) l_assoc RBT.empty"

fun fold_data_shallow where "fold_data_shallow f_str f_self f x accu =
 (\<lambda> ShallB_str s \<Rightarrow> f (f_str s) accu
  | ShallB_self s \<Rightarrow> f (f_self s) accu
  | ShallB_list l \<Rightarrow> List.fold (fold_data_shallow f_str f_self f) l accu
  | _ \<Rightarrow> accu) x"

definition \<open>print_examp_def_st_assoc_build_rbt_gen_typecheck check_ty f_attr_none f_attr map_self map_username l_enum l accu =
 (let v_null = \<open>null\<close>
    ; v_invalid = \<open>invalid\<close> in
  fst (
  List.fold
    (\<lambda> (ocli, cpt) (l, rbt).
      let Inst_name_ocli = inst_name ocli
        ; l = fold_instance_single
                (\<lambda> ty l accu.
                  let f_attr = f_attr ty in
                  fst (List.fold
                  (\<lambda>(pre_post, name_attr, shall) (accu, rbt).
                    let f = \<lambda>msg. \<lambda> None \<Rightarrow> Some msg | _ \<Rightarrow> None
                      ; find_map = \<lambda>x. fold_data_shallow
                                         (\<lambda>s. if s \<triangleq> v_null
                                               | s \<triangleq> v_invalid
                                               | list_ex (\<lambda>OclEnum _ l \<Rightarrow> list_ex ((\<triangleq>) s) l) l_enum then None
                                              else f s (map_username s))
                                         (\<lambda>s. f (\<open>self \<close> @@ String.natural_to_digit10 (case s of Oid n \<Rightarrow> n)) (map_self s))
                                         (\<lambda> None \<Rightarrow> id | Some x \<Rightarrow> Cons x)
                                         x
                                         []
                      ; (accu, rbt) =
                          case case shall of ShallB_list l \<Rightarrow> L.flatten (L.map find_map l)
                                           | _ \<Rightarrow> find_map shall of
                            [] \<Rightarrow> (accu, rbt)
                          | l \<Rightarrow> (* some rhs variables are authorized because some could have been introduced in HOL side (between 2 meta embedded commands) *)
                                 ( if pre_post = None then
                                     (Error, S.flatten [ \<open>Extra variables on rhs: \<close>, String_concatWith \<open>, \<close> (L.map (\<lambda>s. \<open>"\<close> @@ s @@ \<open>"\<close>) l)
                                                     , \<open> in the definition of "\<close>, Inst_name_ocli, \<open>"\<close> ]) # accu
                                   else accu
                                 , rbt)
                      ; (accu, rbt) =
                          if lookup rbt name_attr = None then
                            (accu, insert name_attr () rbt)
                          else
                            ((Warning, S.flatten [ \<open>At least one unused variable "\<close>, name_attr, \<open>"\<close>
                                               , \<open> in the definition of "\<close>, Inst_name_ocli, \<open>"\<close> ]) # accu, rbt) in
                        ( if f_attr name_attr = None then
                            (Error, S.flatten [ \<open>Error in record input: "\<close>, name_attr, \<open>" is no proper field\<close>
                                            , \<open> in the definition of "\<close>, Inst_name_ocli, \<open>"\<close> ]) # accu
                          else accu
                        , rbt))
                  l
                  (accu, RBT.empty)))
                ocli
                (if Inst_name_ocli \<triangleq> v_null
                  | Inst_name_ocli \<triangleq> v_invalid
                  | \<not> f_attr_none Inst_name_ocli (* e.g.: this constant should be (already) defined so that oclAllInstances can receive it as argument *) then
                   (Error, S.flatten [ \<open>Bad head of lhs: existing constant "\<close>, Inst_name_ocli, \<open>"\<close> ]) # l
                 else
                   l)
        ; (l, rbt) =
            ( case check_ty ocli cpt of
                Return_err err \<Rightarrow>
                  fold\<^sub>e\<^sub>r\<^sub>r
                    (\<lambda> Return_err_ty (ty, obj) \<Rightarrow> Cons (Error, S.flatten [ \<open>Type unification failed: Clash of types "\<close>
                                                                       , str_of_ty ty
                                                                       , \<open>" and "\<close>
                                                                       , str_of_data_shallow obj
                                                                       , \<open>"\<close>
                                                                       , \<open> in the definition of "\<close>, Inst_name_ocli, \<open>"\<close> ])
                     | Return_ocl_invalid \<Rightarrow> Cons (Writeln, S.flatten [ \<open>"invalid" returned\<close>
                                                                    , \<open> in the definition of "\<close>, Inst_name_ocli, \<open>"\<close> ])
                     | _ \<Rightarrow> id)
                    err
                    l
              | _ \<Rightarrow> l
            , rbt) in
      (if lookup rbt Inst_name_ocli = None then
         (l, insert Inst_name_ocli () rbt)
       else
         ((Error, S.flatten [ \<open>Duplicate fixed variable(s): "\<close>, Inst_name_ocli, \<open>"\<close> ]) # l, rbt))) l
    (accu, RBT.empty)))\<close>

definition "print_examp_def_st_assoc_build_rbt = print_examp_def_st_assoc_build_rbt_gen (modify_def RBT.empty)"
definition "print_examp_def_st_assoc_build_rbt2 = print_examp_def_st_assoc_build_rbt_gen (\<lambda>_. id)"

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc =
  (let b = \<lambda>s. Term_basic [s]
     ; rbt = print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc in
   Term_app var_map_of_list [Term_list (fold (\<lambda>name. fold (\<lambda>name_attr (l_attr, ty_obj) l_cons.
         let cpt_from = TyObjN_ass_switch (TyObj_from ty_obj) in
         Term_pair
           (Term_basic [print_access_oid_uniq_name cpt_from (\<lambda>s. s @@ String.isub name) name_attr])
           (Term_app \<open>List.map\<close>
             [ Term_binop (let var_x = \<open>x\<close>
                             ; var_y = \<open>y\<close> in
                           Term_lambdas0
                             (Term_pair (b var_x) (b var_y))
                             (Term_list [b var_x, b var_y]))
                          \<open>o\<close>
                          (b (print_access_choose_name
                                (TyObj_ass_arity ty_obj)
                                cpt_from
                                (TyObjN_ass_switch (TyObj_to ty_obj))))
             , Term_list' (Term_list' (Term_list' (Term_oid var_oid_uniq))) l_attr ])
         # l_cons)) rbt [])])"

definition "print_examp_instance_oid thy_definition_hol l env = (L.map thy_definition_hol o L.flatten)
 (let (f1, f2) = (\<lambda> var_oid _ _. var_oid, \<lambda> _ _ cpt. Term_oid \<open>\<close> (oidGetInh cpt)) in
  L.map (\<lambda> (ocli, cpt).
    if List.fold (\<lambda>(_, _, cpt0) b. b | oidGetInh cpt0 = oidGetInh cpt) (D_input_instance env) False then
      []
    else
      let var_oid = Term_oid var_oid_uniq (oidGetInh cpt)
        ; isub_name = \<lambda>s. s @@ String.isub (inst_ty ocli) in
      [Definition (Term_rewrite (f1 var_oid isub_name ocli) \<open>=\<close> (f2 ocli isub_name cpt))]) l)"

definition "check_single = (\<lambda> (name_attr, oid, l_oid) l_mult l.
  let l = (RBT.keys o RBT.bulkload o L.map (\<lambda>x. (x, ()))) l
    ; assoc = \<lambda>x. case map_of l_oid x of Some s \<Rightarrow> s | None \<Rightarrow> case x of Oid n \<Rightarrow> S.flatten [\<open>/*\<close>, String.natural_to_digit10 n, \<open>*/\<close>]
    ; attr_len = natural_of_nat (length l)
    ; l_typed =
       L.map (\<lambda> (mult_min, mult_max0) \<Rightarrow>
         let mult_max = case mult_max0 of None \<Rightarrow> mult_min | Some mult_max \<Rightarrow> mult_max
           ; s_mult = \<lambda> Mult_nat n \<Rightarrow> String.natural_to_digit10 n | Mult_star \<Rightarrow> \<open>*\<close> | Mult_infinity \<Rightarrow> \<open>\<infinity>\<close>
           ; f = \<lambda>s. S.flatten [ \<open> // \<close>
                             , s
                             , \<open> constraint [\<close>
                             , s_mult mult_min
                             , if mult_max0 = None then \<open>\<close> else S.flatten [\<open> .. \<close>, s_mult mult_max]
                             , \<open>] not satisfied\<close> ] in
         L.map (\<lambda> (b, msg) \<Rightarrow> (b, S.flatten [ assoc oid
                                             , \<open> \<close>
                                             , case name_attr of None \<Rightarrow> \<open>/* unnamed attribute */\<close> | Some s \<Rightarrow> \<open>.\<close> @@ s
                                             , \<open> \<cong> Set{\<close> (* '\<cong>' instead of '=' because the lhs can be 'invalid' or 'null'! *)
                                             , let l = L.map assoc l in
                                               if l = [] then \<open>\<close> else \<open> \<close> @@ String_concatWith \<open> , \<close> l @@ \<open> \<close>
                                             , \<open>}\<close>
                                             , if b then \<open>\<close> else f msg ]))
                  [(case mult_min of Mult_nat mult_min \<Rightarrow> mult_min \<le> attr_len | _ \<Rightarrow> True, \<open>minimum\<close>)
                  ,(case mult_max of Mult_nat mult_max \<Rightarrow> mult_max \<ge> attr_len | _ \<Rightarrow> True, \<open>maximum\<close>)]) l_mult
    ; (stop, l_typed) =
       if list_ex (list_all fst) l_typed then
         ( Warning
         , if list_ex (list_ex (Not o fst)) l_typed then
             (* at least 1 warning *)
             L.map (filter (Not o fst)) l_typed
           else
             (* 0 warning *)
             [[hd (hd l_typed)]])
       else
         (Error, L.map (filter (Not o fst)) l_typed) in
  L.flatten (L.map (L.map (\<lambda> (b, s) \<Rightarrow> (if b then Writeln else stop, s))) l_typed))"

definition "check_export_code f_writeln f_warning f_error f_raise l_report msg_last =
 (let l_err =
        List.fold
          (\<lambda> (Writeln, s) \<Rightarrow> \<lambda>acc. case f_writeln s of () \<Rightarrow> acc
           | (Warning, s) \<Rightarrow> \<lambda>acc. case f_warning s of () \<Rightarrow> acc
           | (Error, s) \<Rightarrow> \<lambda>acc. case f_error s of () \<Rightarrow> s # acc)
          l_report
          [] in
  if l_err = [] then
    ()
  else
    f_raise (String.nat_to_digit10 (length l_err) @@ msg_last))"

definition "print_examp_instance_defassoc_gen name l_ocli env =
 (case D_ocl_semantics env of Gen_only_analysis \<Rightarrow> \<lambda>_. [] | Gen_default \<Rightarrow> \<lambda>_. [] | Gen_only_design \<Rightarrow>
  \<lambda>(rbt, (map_self, map_username)).
  let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; l_ocli = if list_ex (\<lambda>(ocli, _). inst_ty0 ocli = None) l_ocli then [] else l_ocli in
  [Definition
     (Term_rewrite name
     \<open>=\<close>
     (let var_oid_class = \<open>oid_class\<close>
        ; var_to_from = \<open>to_from\<close>
        ; var_oid = \<open>oid\<close>
        ; a_l = \<lambda>s. Typ_apply (Typ_base var_ty_list) [s] in
      Term_lambdas
        [var_oid_class, var_to_from, var_oid]
        (Term_annot (Term_case
          (Term_app var_deref_assocs_list
            [ Term_annot (b var_to_from) (Ty_arrow
                                            (a_l (a_l (Typ_base const_oid)))
                                            (let t = a_l (Typ_base const_oid) in
                                             Ty_times t t))
            , Term_annot' (b var_oid) const_oid
            , a \<open>drop\<close>
              (Term_applys (print_examp_def_st_assoc (snd o rbt) map_self map_username l_ocli)
                           [Term_annot' (b var_oid_class) const_oid])])
          [ (b \<open>Nil\<close>, b \<open>None\<close>)
          , let b_l = b \<open>l\<close> in
            (b_l, a \<open>Some\<close> b_l)] ) (Typ_apply (Typ_base \<open>option\<close>) [a_l (Typ_base const_oid)]))))])"

definition "check_single_ty rbt_init rbt' l_attr_gen l_oid x =
 (\<lambda> (ty1, mult1) (ty2, mult2).
  let role1 = TyRole mult1
    ; role2 = TyRole mult2
    ; s = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; s' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; s'' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; (name, (mult_from, mult_to), l) =
        case
          let f = \<lambda>g.
            \<lambda> None \<Rightarrow> None
            | Some role1 \<Rightarrow>
                map_option
                  (\<lambda>_. let (ty1, role1, f_swap) = g role1 in
                       ( case fst (rbt_init ty1) role1 of Some (OclTy_object (OclTyObj (OclTyCore ty_obj) _), _, _) \<Rightarrow> ty_obj
                       , f_swap (TyObj_from, TyObj_to)))
                  (lookup rbt' role1) in
          case role2 of
             None \<Rightarrow> f (\<lambda>role1. (ty2, role1, \<lambda>(a, b). (b, a))) role1
           | Some role2 \<Rightarrow>
              (case lookup rbt' role2 of
                Some (_, ty_obj) \<Rightarrow> Some (ty_obj, (TyObj_from, TyObj_to))
              | None \<Rightarrow> f (\<lambda>_. (ty1, role2, id)) role1)
        of
          Some (ty_obj, (f_from, f_to)) \<Rightarrow>
            let (o_from, o_to) = (f_from ty_obj, f_to ty_obj) in
            ( case (TyObjN_role_name o_from, TyObjN_role_name o_to) of
                (name_from, name_to) \<Rightarrow> [name_from, name_to]
            , (TyObjN_role_multip o_from, TyObjN_role_multip o_to)
            , deref_assocs_list s x (L.map (if ( TyObjN_ass_switch o_from
                                                  , TyObjN_ass_switch o_to) = (0, 1) then(*01*) id else(*10*) rev)
                                              (case l_attr_gen (TyObj_ass_id ty_obj) of Some l_attr \<Rightarrow> l_attr)))
        | None \<Rightarrow> ([role1, role2], (mult1, mult2), []) in
  (\<lambda>acc.
    L.flatten [ acc
            , check_single
                ((snd o s'') name, x, l_oid)
                ((snd o s') ([TyMult mult_from, TyMult mult_to]))
                l]))"

definition "mk_instance_single_cpt0 map_username l env =
 (let (l, cpt) =
  L.mapM (\<lambda>ocli cpt. case Inst_attr_with ocli of
                       None \<Rightarrow> ([(ocli, cpt)], oidSucInh cpt)
                     | Some n \<Rightarrow>
                       (case map_username n of None \<Rightarrow> ([(ocli, cpt)], oidSucInh cpt)
                                             | Some cpt' \<Rightarrow> ([(ocli, cpt')], cpt)))
         l
         (D_ocl_oid_start env) in
  (L.flatten l, cpt))"

definition "mk_instance_single_cpt map_username l =
  fst o mk_instance_single_cpt0 map_username l"

definition "print_examp_instance_defassoc = (\<lambda> OclInstance l \<Rightarrow> \<lambda> env.
  let (rbt :: _ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (ocl_ty \<times> ocl_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
      , (map_self, map_username)) = init_map_class env l
    ; l = mk_instance_single_cpt map_username l env in
  (\<lambda>l_res.
    ( print_examp_instance_oid O.definition l env
      @@@@ L.map O.definition l_res
    , env))
  (print_examp_instance_defassoc_gen
    (Term_oid var_inst_assoc (oidGetInh (D_ocl_oid_start env)))
    l
    env
    (rbt, (map_self, map_username))))"

definition "fold_instance_single_name ocli =
 (let b = \<lambda>s. Term_basic [s] in
  (case Inst_attr_with ocli of None \<Rightarrow> id
                             | Some s \<Rightarrow> Cons (b s))
  o
  fold_instance_single' (\<lambda>_. List.fold (\<lambda> (_, _, d). fold_data_shallow Some
                                                                       (\<lambda>_. None)
                                                                       (\<lambda> Some s \<Rightarrow> Cons (b s) | None \<Rightarrow> id)
                                                                       d))
                        ocli)"

definition "print_examp_instance_defassoc_typecheck_var = (\<lambda> OclInstance l \<Rightarrow>
 (let b = \<lambda>s. Term_basic [s]
    ; l_var = List.fold (\<lambda>ocli. case Inst_name ocli of None \<Rightarrow> id | Some n \<Rightarrow> Cons n) l []
    ; n = \<open>_\<close> @@ String_concatWith \<open>_\<close> l_var in
  Pair
    [ O.definition
        (Definition
          (Term_rewrite
            (Term_app (\<open>typecheck_instance_bad_head_on_lhs\<close> @@ n) (L.map b l_var))
            \<open>=\<close>
            (Term_pair' [])))
    , O.definition
        (Definition
          (Term_rewrite
            (b (\<open>typecheck_instance_extra_variables_on_rhs\<close> @@ n))
            \<open>=\<close>
            (Term_lambdas l_var (Term_pair' (List.fold fold_instance_single_name l [])))))]))"

definition "print_examp_instance_app_constr2_notmp_norec = (\<lambda>(rbt, (map_self, map_username)) cpt_start ocli isub_name cpt.
  let l_attr = split_inh_own rbt (inst_ty ocli) (Inst_attr ocli) in
  ( print_examp_instance_app_constr2_notmp
      l_attr
      isub_name
      cpt
      (\<lambda>isub_name oid.
        ( \<lambda> ty_obj.
            let b = \<lambda>s. Term_basic [s] in
            Return_val
              (Term_applys
                cpt_start
                (let ty_objfrom = TyObj_from ty_obj
                   ; ty_objto = TyObj_to ty_obj in
                 [ b (print_access_oid_uniq_name (TyObjN_ass_switch ty_objfrom) isub_name (case TyObjN_role_name ty_objto of Some s \<Rightarrow> s))
                 , b (print_access_choose_name (TyObj_ass_arity ty_obj) (TyObjN_ass_switch ty_objfrom) (TyObjN_ass_switch ty_objto))
                 , Term_oid var_oid_uniq (oidGetInh oid) ]))
        , \<lambda> base.
            let f = \<lambda>v. \<lambda> None \<Rightarrow> Return_err v
                        | Some s \<Rightarrow> Return_val ((Term_oid var_oid_uniq o oidGetInh) s) in
            case base of (_, ShallB_str s) \<Rightarrow> f (Return_object_variable s) (map_username s)
                       | (_, ShallB_self cpt1) \<Rightarrow> f (Return_err_ty base) (map_self cpt1)
                       | _ \<Rightarrow> Return_err (Return_err_ty base)))
  , Term_warning_parenthesis o print_examp_instance_app_constr2_notmp' l_attr))"

definition \<open>print_examp_instance_defassoc_typecheck_gen l_ocli env =
 (let l_enum = List.map_filter (\<lambda>META_enum e \<Rightarrow> Some e | _ \<Rightarrow> None) (D_input_meta env)
    ; (l_spec1, l_spec2) = arrange_ass False True (fst (find_class_ass env)) l_enum in

  case class_unflat (l_spec1, l_spec2) of None \<Rightarrow> [ raise_ml [(Error, \<open>The universe of classes contains a cycle\<close>)]
                                                             \<open> error(s)\<close> ]
                                        | Some spec \<Rightarrow> (* cycles could still occur, but not in "spec" *)
  let raise_ml_warn = \<lambda>s raise_ml l. raise_ml ((Warning, s) # l)
    ; raise_ml =
      (if length l_spec1 + (if list_ex (\<lambda> c. cl_name_to_string c \<triangleq> const_oclany) l_spec1 then 0 else 1)
          > nb_class spec then
         raise_ml_warn (\<open>Some classes have been ignored because of duplications of classes, the absence of classes inheriting from OclAny or the presence of cycles.\n\<close> @@
                        \<open>The classes considered for the generation are only:\n  \<close> @@
                         String_concatWith \<open>, \<close>
                           (rev (fst (fold_class (\<lambda> _ name _ _ _.
                                                   \<lambda> [] \<Rightarrow> Pair name
                                                   | l \<Rightarrow> Pair (name @@ \<open>[\<close> @@ String_concatWith \<open>, \<close> (L.map (\<lambda> OclClass n _ _ \<Rightarrow> n) l) @@ \<open>]\<close>))
                                                 ()
                                                 spec))))
       else id)
      raise_ml
    ; raise_ml =
      (case
         RBT.entries (List.fold (\<lambda> c l.
                     snd (List.fold (\<lambda> (s, _) (rbt, l).
                                       case lookup rbt s of
                                         None \<Rightarrow> (insert s () rbt, l)
                                       | Some _ \<Rightarrow> (rbt, insert s (cl_name_to_string c) l))
                                    (ClassRaw_own c)
                                    (RBT.empty, l)))
                   l_spec1
                   RBT.empty) of
         [] \<Rightarrow> id
       | l \<Rightarrow> raise_ml_warn (\<open>Duplicate constant declaration:\n\<close> @@
                             String_concatWith \<open>\n\<close> (L.map (\<lambda>(s, name). \<open>  \<close> @@ name @@ \<open>: \<close> @@ \<lless>s\<ggreater>) l)))
      raise_ml
    ; raise_ml =
      (case
         L.map fst
           (RBT.entries
             (List.fold
               (\<lambda>ass accu. case OclAss_relation ass of OclAssRel l \<Rightarrow>
                 snd (List.fold (\<lambda>(_, m).
                                   case TyRole m of None \<Rightarrow> id
                                   | Some name \<Rightarrow> \<lambda>(rbt, accu).
                                      (case lookup rbt name of None \<Rightarrow> (insert name () rbt, accu)
                                                             | Some _ \<Rightarrow> (rbt, insert name () accu)))
                                l
                                (RBT.empty, accu)))
               l_spec2
               RBT.empty)) of
         [] \<Rightarrow> id
       | l \<Rightarrow> raise_ml_warn (\<open>Duplicate constant declaration in association:\n\<close> @@
                             String_concatWith \<open>\n\<close> (L.map (\<lambda>s. \<open>  \<close> @@ \<lless>s\<ggreater>) l)))
      raise_ml
    ; env = env \<lparr> D_input_class := Some spec \<rparr>
    ; l_assoc = List.map_filter id l_ocli in
  if list_ex (\<lambda>ocli. inst_ty0 ocli = None) l_assoc then
    [ raise_ml
        (List.map_filter (\<lambda>ocli. if inst_ty0 ocli = None then Some (Error, \<open>Missing type annotation in the definition of "\<close> @@ inst_name ocli @@ \<open>"\<close>) else None) l_assoc)
        \<open> error(s)\<close>]
  else
    let (rbt_init0, (map_self, map_username)) = init_map_class env (L.map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> ocl_instance_single_empty) l_ocli)
      ; rbt_init = snd o rbt_init0
      ; l_assoc = mk_instance_single_cpt map_username l_assoc env
      ; rbt = print_examp_def_st_assoc_build_rbt2 rbt_init map_self map_username l_assoc
      ; l_attr_gen = map_of_list (fold (\<lambda>_ (l_attr, ty_obj).
             Cons ( TyObj_ass_id ty_obj
                  , L.map ( (\<lambda>(x , y). [x , y])
                             o (if TyObjN_ass_switch (TyObj_from ty_obj) < TyObjN_ass_switch (TyObj_to ty_obj) then
                                  (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                                else
                                  (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)))
                             l_attr)) rbt [])
      ; l_oid_gen = L.map
          (\<lambda> (ocli, oids).
            ( fst (hd (fold_instance_single (\<lambda>a b. Cons (a, b)) ocli []))
            , case oidGetInh oids of oid \<Rightarrow> oid
            , inst_name ocli ))
          l_assoc in
    case L.split l_oid_gen of (_, l_oid) \<Rightarrow>
    let l_out =
      List.fold
        (\<lambda> (name, (x, _)).
          let l = find_inh name spec
            ; f = \<lambda>(ty1, mult1) ty2 accu.
            fst (List.fold
              (\<lambda> ty1' (l, b).
                if b then
                  (l, b)
                else
                  ( check_single_ty rbt_init rbt l_attr_gen l_oid x (ty1', mult1) ty2 l
                  , ty1' \<triangleq> ty1))
              (if name \<triangleq> ty1 then
                 ty1 # l
               else if list_ex ((\<triangleq>) ty1) l then
                 l
               else
                 [])
              (accu, False)) in
          List.fold (\<lambda>ass.
                       case L.map (map_prod ty_obj_to_string id) (OclAss_relation' ass) of
                         [t1, t2] \<Rightarrow> f t2 t1 o f t1 t2
                       | _ \<Rightarrow> id)
                    l_spec2)
        l_oid_gen
        [] in

    [ raise_ml
        (L.flatten [ rev (print_examp_def_st_assoc_build_rbt_gen_typecheck
                               (\<lambda>ocli. fst o print_examp_instance_app_constr2_notmp_norec (snd o rbt_init0, (map_self, map_username)) (Term_basic []) ocli id)
                               (fst o rbt_init0)
                               (fst o rbt_init)
                               map_self
                               map_username
                               l_enum
                               l_assoc
                               [])
                      , l_out])
        \<open> error(s)\<close> ])\<close>

definition "print_examp_instance_defassoc_typecheck = (\<lambda> OclInstance l \<Rightarrow> \<lambda> env.
  (\<lambda>l_res. (L.map O.ML l_res, env \<lparr> D_output_header_force := True \<rparr>))
  (print_examp_instance_defassoc_typecheck_gen
    (L.map Some l)
    env))"

definition "print_examp_instance_name = id"
definition "print_examp_instance = (\<lambda> OclInstance l \<Rightarrow> \<lambda> env.
 (\<lambda> ((l_res, oid_start), instance_rbt).
    ((L.map O.definition o L.flatten) l_res, env \<lparr> D_ocl_oid_start := oid_start, D_input_instance := instance_rbt \<rparr>))
  (let (rbt, (map_self, map_username)) = init_map_class env l
     ; a = \<lambda>f x. Term_app f [x]
     ; b = \<lambda>s. Term_basic [s] in
   ( let var_inst_ass = \<open>inst_assoc\<close> in
     map_prod
       (L.map
         (\<lambda> (ocli, cpt).
           let var_oid = Term_oid var_oid_uniq (oidGetInh cpt)
             ; (isub_name, body2, body2') =
                 case inst_ty0 ocli of
                   Some ty \<Rightarrow>
                       let isub_name = \<lambda>s. s @@ String.isub (inst_ty ocli) in
                       (isub_name, print_examp_instance_app_constr2_notmp_norec (snd o rbt, (map_self, map_username)) (b var_inst_ass) ocli isub_name cpt)
                 | None \<Rightarrow> (id, (Return_err Return_err_ty_auto, id))
             ; l =
               [ Definition
                   (Term_rewrite (let e = b (inst_name ocli) in
                                  case Inst_ty ocli of
                                    None \<Rightarrow> e
                                  | Some ty \<Rightarrow> Term_annot_ocl e ty)
                                 \<open>=\<close>
                                 (case body2 of Return_err _ \<Rightarrow> b \<open>invalid\<close>
                                              | _ \<Rightarrow> body2' (Term_lambda
                                                               wildcard
                                                               (Term_some (Term_some (let name_pers = print_examp_instance_name isub_name (inst_name ocli) in
                                                                                      if D_ocl_semantics env = Gen_only_design then
                                                                                        a name_pers (Term_oid var_inst_assoc (oidGetInh (D_ocl_oid_start env)))
                                                                                      else
                                                                                        b name_pers))))))] in
           case body2 of Return_err _ \<Rightarrow> l
                       | Return_val body2 \<Rightarrow> Definition (Term_rewrite (Term_basic (print_examp_instance_name isub_name (inst_name ocli)
                                                                                   # (if D_ocl_semantics env = Gen_only_design then [ var_inst_ass ] else [])))
                                                                      \<open>=\<close>
                                                                      body2)
                                             # l))
       id
       (mk_instance_single_cpt0 map_username l env)
   , let l_id = L.mapi (\<lambda>i ocli. (i, inst_name ocli)) l in
     List.fold
       (\<lambda>ocli instance_rbt.
         let n = inst_name ocli in
         ( String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e n
         , map_inst_single_self (\<lambda>Oid self \<Rightarrow>
                                  case L.assoc self l_id of
                                    Some name \<Rightarrow> ShallB_str name
                                  | _ \<Rightarrow> ShallB_list [])
                                ocli
         , case map_username n of Some oid \<Rightarrow> oid)
         # instance_rbt)
       l
       (D_input_instance env))))"

definition "print_examp_def_st_typecheck_var = (\<lambda> OclDefSt name l \<Rightarrow>
 (let b = \<lambda>s. Term_basic [s]
    ; l_var0 = [name]
    ; n = \<open>_\<close> @@ String_concatWith \<open>_\<close> l_var0 in
  Pair
    [ O.definition
        (Definition
          (Term_rewrite
            (Term_app (\<open>typecheck_state_bad_head_on_lhs\<close> @@ n) (L.map b l_var0))
            \<open>=\<close>
            (Term_pair' [])))
    , O.definition
        (Definition
          (Term_rewrite
            (b (\<open>typecheck_state_extra_variables_on_rhs\<close> @@ n))
            \<open>=\<close>
            (Term_pair' (List.fold (\<lambda> OclDefCoreAdd i \<Rightarrow> fold_instance_single_name i
                                    | OclDefCoreBinding s \<Rightarrow> Cons (b s))
                                   l
                                   []))))]))"

definition "print_examp_def_st0 name l =
 (let (l, _) = List.fold (\<lambda> (pos, core) (l, n).
                                      ((pos, pos - n, core) # l,
                                        case core of OclDefCoreAdd _ \<Rightarrow> n
                                        | OclDefCoreBinding _ \<Rightarrow> Succ n))
                             (L.mapi Pair l)
                             ([], 0) in
  List.fold (\<lambda> (pos, _, OclDefCoreAdd ocli) \<Rightarrow> \<lambda>(l_inst, l_defst).
               let i_name = case Inst_name ocli of Some x \<Rightarrow> x | None \<Rightarrow> S.flatten [name, \<open>_object\<close>, String.natural_to_digit10 pos] in
                 ( map_inst_single_self (\<lambda>Oid self \<Rightarrow>
                     (case L.assoc self l of
                        Some (_, OclDefCoreBinding name) \<Rightarrow> ShallB_str name
                      | Some (p, _) \<Rightarrow> ShallB_self (Oid p)
                      | _ \<Rightarrow> ShallB_list [])) ocli
                   \<lparr> Inst_name := Some i_name \<rparr>
                 # l_inst
                 , OclDefCoreBinding i_name # l_defst)
             | (_, _, OclDefCoreBinding name) \<Rightarrow> \<lambda>(l_inst, l_defst).
                 ( l_inst
                 , OclDefCoreBinding name # l_defst))
            l
            ([], []))"

definition "print_examp_increase_oid l_inst =
  snd o print_examp_instance (OclInstance l_inst)"

definition "bootstrap_floor' f_x l env =
 (let (l, accu :: compiler_env_config \<Rightarrow> _) = f_x l env in
  (bootstrap_floor l env, accu))"

definition "print_examp_def_st1_gen = (\<lambda> OclDefSt name l \<Rightarrow> bootstrap_floor'
  (\<lambda>(l, accu) _. (L.flatten [L.map META_all_meta_embedding l], accu))
  (let (l_inst, l_defst) = print_examp_def_st0 name l
     ; l = [ META_def_state Floor2 (OclDefSt name l_defst) ] in
   if l_inst = [] then
     (l, id)
   else
     (META_instance (OclInstance l_inst) # l, print_examp_increase_oid l_inst)))"

definition "print_examp_def_st1 s = fst o print_examp_def_st1_gen s"
definition "print_meta_setup_def_state s env = snd (print_examp_def_st1_gen s env) env"

definition "print_examp_def_st_defs = (\<lambda> _ \<Rightarrow> start_map O.lemmas
  [ Lemmas_simp_thms \<open>\<close> [ \<open>state.defs\<close>, \<open>const_ss\<close> ] ])"

definition "print_transition_gen = (\<lambda> OclDefPP name s_pre s_post \<Rightarrow> bootstrap_floor'
  (\<lambda>f env.
    let (l, accu) = f env in
    (L.flatten [ L.map META_all_meta_embedding l ], accu))
  (\<lambda>env.
    let pref_name = case name of Some n \<Rightarrow> n
                               | None \<Rightarrow> \<open>WFF_\<close> @@ String.nat_to_digit10 (length (D_input_meta env))
      ; f_comp = \<lambda>None \<Rightarrow> id | Some (_, f, _) \<Rightarrow> f
      ; f_comp_env = \<lambda>None \<Rightarrow> id | Some (_, _, f) \<Rightarrow> f
      ; f_conv = \<lambda>msg.
          \<lambda> OclDefPPCoreAdd ocl_def_state \<Rightarrow>
              let n = pref_name @@ msg in
              ( OclDefPPCoreBinding n
              , Cons (META_def_state Floor1 (OclDefSt n ocl_def_state))
              , let l_inst = fst (print_examp_def_st0 n ocl_def_state) in
                if l_inst = [] then id else print_examp_increase_oid l_inst )
          | s \<Rightarrow> (s, id, id)
      ; o_pre = Some (f_conv \<open>_pre\<close> s_pre)
      ; o_post = map_option (f_conv \<open>_post\<close>) s_post in
    ( (f_comp o_pre o f_comp o_post)
       [ META_def_transition Floor2 (OclDefPP name
                                           (case o_pre of Some (n, _) \<Rightarrow> n)
                                           (map_option fst o_post)) ]
    , f_comp_env o_pre o f_comp_env o_post )))"

definition "print_transition s = fst o print_transition_gen s"
definition "print_meta_setup_def_transition s env = snd (print_transition_gen s env) env"

end
