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

section\<open>Main Translation for: Context (Floor 2)\<close>

theory  Floor2_ctxt
imports Core_init
begin

(* (* ERROR this lambda term type-checks expensively *)
definition "print_ctxt_is_accessor =
  (\<lambda> Type \<lless>''fun''\<ggreater>
               [Type \<lless>''fun''\<ggreater>
                       [Type \<lless>''Product_Type.prod''\<ggreater>
                               [Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Type _ (* AA *) [], Type \<lless>''Product_Type.unit''\<ggreater> []],
                                Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Type _ (* AA *) [], Type \<lless>''Product_Type.unit''\<ggreater> []]],
                        TFree _ (* 'a *) [\<lless>''HOL.type''\<ggreater>]],
                Type \<lless>''fun''\<ggreater>
                       [Type \<lless>''Product_Type.prod''\<ggreater>
                               [Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Type _ (* AA *) [], Type \<lless>''Product_Type.unit''\<ggreater> []],
                                Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Type _ (* AA *) [], Type \<lless>''Product_Type.unit''\<ggreater> []]],
                        Type \<lless>''Option.option''\<ggreater>
                               [Type \<lless>''Option.option''\<ggreater>
                                       [Type _ (* class name *) []]]]]
       \<Rightarrow> True
   | _ \<Rightarrow> False)"
*)
definition "print_ctxt_is_name_at_gen var s =
 (let var = String.to_list var
    ; s = String.to_list s in
  case var of _ # _ \<Rightarrow>
    let lg_var = length var in
    if (* TODO use \<triangleq> *) L.take_last lg_var s = var then
      Some \<lless>L.take_first (length s - lg_var) s\<ggreater>
    else
      None)"

definition "print_ctxt_is_name_at_pre = print_ctxt_is_name_at_gen var_at_when_hol_pre"
definition "print_ctxt_is_name_at_post = (case String.to_list var_at_when_hol_post of [] \<Rightarrow>
  \<lambda>s. case print_ctxt_is_name_at_pre s of None \<Rightarrow> Some s
                                        | _ \<Rightarrow> None)"

definition "print_ctxt_to_ocl_gen_split s =
 (case L.split_at (\<lambda> s. s = CHR 0x2E) (String.to_list s) of
    (_, Some _, s) \<Rightarrow> Some s
  | _ \<Rightarrow> None)"
definition "print_ctxt_to_ocl_gen l_access f var =
 (let l_ex = \<lambda>s. (*print_ctxt2_is_accessor ty*)
                 list_ex (case print_ctxt_to_ocl_gen_split s of
                            Some s \<Rightarrow> \<lambda>n. String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list n = s
                          | _ \<Rightarrow> \<lambda>_. False) l_access in
  \<lambda> T_pure t o_s \<Rightarrow>
  T_pure (Meta_Pure.map_Const (\<lambda> s _.
            if l_ex s then
              case f s of
                Some s \<Rightarrow> s @@ var
              | _ \<Rightarrow> s
            else
              s) t)
         (if Meta_Pure.fold_Const (\<lambda> b s. b | l_ex s & f s \<noteq> None) False t then
            None
          else
            o_s))"

definition "print_ctxt_to_ocl_pre env = print_ctxt_to_ocl_gen (snd (D_ocl_accessor env)) print_ctxt_is_name_at_post var_at_when_hol_pre"
definition "print_ctxt_to_ocl_post env = print_ctxt_to_ocl_gen (fst (D_ocl_accessor env)) print_ctxt_is_name_at_pre var_at_when_hol_post"

definition "raise_ml_unbound f_msg ctxt =
        [ (\<lambda>_. [O.ML (raise_ml (let l = L.flatten (L.mapi (\<lambda> n. \<lambda>(msg, T_pure t _) \<Rightarrow>
                                            let l =
                                              rev (Meta_Pure.fold_Free (\<lambda>l s.
                                                (Error, S.flatten [f_msg n msg, \<open>: unbound value \<close>, s]) # l) [] t) in
                                            if l = [] then [(Writeln, f_msg n msg)] else l) ctxt) in
                                 if list_ex (\<lambda>(Error, _) \<Rightarrow> True | _ \<Rightarrow> False) l then l else [])
                                \<open> error(s)\<close>)]) ]"

definition "print_ctxt_pre_post_interp = (\<lambda>(sorry, dirty) name ctxt e_name e_pre e_post.
  let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; f = \<lambda>(pref, e). List.foldr Term_lambda (make_ctxt_free_var pref ctxt) e
    ; lg = length (Ctxt_fun_ty_arg ctxt) in
  if (sorry = Some Gen_sorry | sorry = None & dirty) & lg \<le> 3 then
    Some (O.interpretation
      (Interpretation
        name
        (\<open>contract\<close> @@ String.nat_to_digit10 lg)
        [ e_name
        , f e_pre
        , f e_post ]
        (*apply(unfold_locales, simp only: dot__aaa_Person Let_def, auto)*)
        C.sorry))
  else
    None (* not yet implemented *))"

definition "print_ctxt_pre_post = (\<lambda>f. map_prod L.flatten id o f) o L.mapM (\<lambda>x env. (x env, env)) o (\<lambda> ctxt.
 let ty_name = ty_obj_to_string (Ctxt_ty ctxt) in
 L.flatten (L.map (\<lambda> (l_ctxt, ctxt).
  let (l_pre, l_post) = List.partition (\<lambda> (OclCtxtPre, _) \<Rightarrow> True | _ \<Rightarrow> False) l_ctxt
    ; attr_n = Ctxt_fun_name ctxt
    ; a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; var_tau = \<open>\<tau>\<close>
    ; f_tau = \<lambda>s. Term_warning_parenthesis (Term_binop (b var_tau) \<open>\<Turnstile>\<close> (Term_warning_parenthesis s))
    ; term_binop0 = \<lambda>base u_and. \<lambda> [] \<Rightarrow> b base | l \<Rightarrow> Term_parenthesis (term_binop u_and l)
    ; to_s = \<lambda>pref f_to l_pre.
        Term_parenthesis (term_binop0 \<open>true\<close> \<open>and\<close>
          (L.map
             (let nb_var = length (make_ctxt_free_var pref ctxt) in
              (\<lambda>(_, expr) \<Rightarrow>
                 cross_abs (\<lambda>_. id) nb_var (case f_to expr of T_pure expr _ \<Rightarrow> expr))) l_pre))
    ; f = \<lambda> (var_at_when_hol, var_at_when_ocl).
        let dot_expr = \<lambda>e f_escape. Term_postunary e (b (mk_dot_par_gen (S.flatten [\<open>.\<close>, attr_n, var_at_when_ocl]) (L.map (f_escape o fst) (Ctxt_fun_ty_arg ctxt)))) in
        (\<lambda>env.
            let (l_pre, l_post) = ( to_s OclCtxtPre (print_ctxt_to_ocl_pre env) l_pre
                                      , to_s OclCtxtPost id l_post)
              ; var_r = var_result
              ; expr =
              Term_rewrite
                (dot_expr (Term_annot_ocl (b var_self) ty_name) id)
                \<open>\<equiv>\<close>
                (Term_lambda var_tau
                  (a \<open>Eps\<close> (Term_lambda var_r
                                        (Term_app \<open>HOL.Let\<close>
                                          [ Term_lambda \<open>_\<close> (b var_r)
                                          , Term_lambda var_result
                                                        (Term_parenthesis (Term_if_then_else (term_binop0 \<open>True\<close> \<open>\<and>\<close> (f_tau (a \<open>\<delta>\<close> (b var_self)) # L.map (\<lambda>s. f_tau (a \<open>\<upsilon>\<close> (b (fst s)))) (Ctxt_fun_ty_arg ctxt)))
                                                                                             (Term_binop
                                                                                               (f_tau l_pre)
                                                                                               \<open>\<and>\<close>
                                                                                               (f_tau l_post))
                                                                                             (f_tau (Term_rewrite (b var_result) \<open>\<triangleq>\<close> (b \<open>invalid\<close>)))))]))))
              ; (name0, def) =
                 (if
                    List.fold (\<lambda> (_, T_pure t _) \<Rightarrow> \<lambda> b \<Rightarrow>
                                 b | Meta_Pure.fold_Const (\<lambda> b s. b | (case print_ctxt_to_ocl_gen_split s of
                                                               None \<Rightarrow> False
                                                             | Some s \<Rightarrow>
                                                                 let f_eq = \<lambda>a. String.to_list (print_ctxt_const_name attr_n a None) = s in
                                                                 f_eq var_at_when_hol_post | f_eq var_at_when_hol_pre))
                                                False
                                                t)
                              l_ctxt
                              False
                  then
                    ( print_ctxt_pre_post_name attr_n var_at_when_hol
                    , O.axiomatization (Axiomatization (print_ctxt_pre_post_name attr_n var_at_when_hol (Some ty_name)) expr))
                  else
                    ( print_ctxt_const_name attr_n var_at_when_hol
                    , O.overloading (Overloading' (print_ctxt_const_name attr_n var_at_when_hol None)
                                                  (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty ty_name))))
                                                  (print_ctxt_const_name attr_n var_at_when_hol (Some ty_name))
                                                  expr)))
              ; name = name0 (Some ty_name) in
            def
            # O.thm (Thm [T.thm name])
            # (case let name = name0 None in
                    print_ctxt_pre_post_interp
                      (D_output_sorry_dirty env)
                      name
                      ctxt
                      (let v = b var_self in
                       Term_lambdas0 (Term_annot_ocl v ty_name) (a name v))
                      (OclCtxtPre, l_pre)
                      (OclCtxtPost, l_post) of
                 None \<Rightarrow> []
               | Some x \<Rightarrow> [x]))
        # (\<lambda>env.
            L.flatten (fst (fold_class (\<lambda>_ name _ _ _ _.
              Pair (if ty_name \<triangleq> name then
                      []
                    else
                      let var_x = \<open>x\<close>
                        ; f_escape = \<lambda>s. var_x @@ String.isub s in
                      [ O.overloading
                          (Overloading' (S.flatten [ \<open>dot\<close>, String.isup attr_n, var_at_when_hol])
                                        (Ty_arrow' (Ty_paren (Typ_base (wrap_oclty name))))
                                        (S.flatten [ \<open>dot\<close>, String.isup attr_n, var_at_when_hol, \<open>_\<close>, name])
                                            (Term_rewrite
                                              (dot_expr (Term_annot_ocl (b var_x) name) f_escape)
                                              \<open>\<equiv>\<close>
                                              (dot_expr (Term_postunary (b var_x) (b (dot_astype ty_name))) f_escape))) ]))
                  ()
                  (case D_input_class env of Some class_spec \<Rightarrow> class_spec))))
        # raise_ml_unbound
          (\<lambda>n pref. S.flatten [\<open>(\<close>, String.natural_to_digit10 (n + 1), \<open>) \<close>, if pref = OclCtxtPre then \<open>pre\<close> else \<open>post\<close>])
          l_ctxt in
  f (var_at_when_hol_post, var_at_when_ocl_post))
  (rev (fold_pre_post (\<lambda> l c. Cons (L.map (map_prod id snd) l, c)) ctxt []))))"

definition "print_ctxt_inv = (\<lambda>f. map_prod L.flatten id o f) o L.mapM (\<lambda>x env. (x env, env)) o L.flatten o L.flatten o (\<lambda> ctxt.
  let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; f_tau = \<lambda>s. Term_lam \<open>\<tau>\<close> (\<lambda>var_tau. Term_warning_parenthesis (Term_binop (b var_tau) \<open>\<Turnstile>\<close> s))
    ; nb_var = length (Ctxt_param ctxt)
    ; Ctxt_ty_n = ty_obj_to_string (Ctxt_ty ctxt)
    ; l = fold_invariant' ctxt in

 L.map (\<lambda> (tit, term) \<Rightarrow>
    (L.map
      (\<lambda> (allinst_at_when, var_at_when, e) \<Rightarrow>
        [ (\<lambda>env. [ O.definition
                     (Definition (Term_rewrite
                                   (b (print_ctxt_inv_name Ctxt_ty_n tit var_at_when))
                                   \<open>=\<close>
                                   (f_tau (cross_abs (\<lambda>s x. Term_app var_OclForall_set
                                                              [ a allinst_at_when (b Ctxt_ty_n)
                                                              , Term_lambda s x])
                                                     (Suc nb_var (* nb_var + \<open>self\<close> *))
                                                     (case e env of T_pure e _ \<Rightarrow> e)) )))]) ])
      [(\<open>OclAllInstances_at_pre\<close>, var_at_when_hol_pre, \<lambda>env. print_ctxt_to_ocl_pre env term)
      ,(\<open>OclAllInstances_at_post\<close>, var_at_when_hol_post, \<lambda>env. print_ctxt_to_ocl_post env term)])
  @@@@ [raise_ml_unbound (\<lambda>_ pref. S.flatten [\<open>inv \<close>, pref]) l])
    l)"

definition "print_ctxt_thm ctxt = Pair
 (case L.flatten (L.map (\<lambda>(tit, _). L.map (hol_definition o print_ctxt_inv_name (ty_obj_to_string (Ctxt_ty ctxt)) tit)
                                                   [ var_at_when_hol_pre
                                                   , var_at_when_hol_post ])
                              (fold_invariant' ctxt)) of
    [] \<Rightarrow> []
  | l \<Rightarrow> [ O.thm (Thm (L.map T.thm l)) ])"

end
