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

section\<open>Main Translation for: Context (Floor 1)\<close>

theory  Floor1_ctxt
imports Core_init
begin

definition "print_ctxt_const ctxt env =
 (let Ty_par = Typ_apply_paren \<open>(\<close> \<open>)\<close> (* because of potential ambiguities *)
    ; l_enum = List.map_filter (\<lambda> META_enum e \<Rightarrow> Some e | _ \<Rightarrow> None) (D_input_meta env)
    ; l_syn = List.map_filter (\<lambda> META_class_synonym c \<Rightarrow> Some c | _ \<Rightarrow> None) (D_input_meta env) in
  map_prod (map_prod id (rev o L.map O.type_synonym)) (rev o L.map O.consts)
    (List.fold
      (\<lambda> Ctxt_inv _ \<Rightarrow> id
       | Ctxt_pp ctxt \<Rightarrow>
          let attr_n = Ctxt_fun_name ctxt in
          List.fold
            (\<lambda>(var_at_when_hol, var_at_when_ocl, f_update_ocl) ((env, l_isab_ty), l_isab_const).
              let name = print_ctxt_const_name attr_n var_at_when_hol None
                ; (l_name, l) =
                    List.fold
                      (\<lambda> ty (l_name, l, l_isab_ty).
                        let ty = map_enum_syn l_enum l_syn ty
                          ; (n, isab_ty) = print_infra_type_synonym_class_rec_aux ty in
                        ( Ty_par (print_access_dot_consts_ty ty) # l_name
                        , if is_higher_order ty & \<not> String.member l n then
                            (String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e n # l, Type_synonym' n isab_ty # l_isab_ty)
                          else
                            (l, l_isab_ty)))
                      (L.flatten
                          [ L.map snd (Ctxt_fun_ty_arg ctxt)
                          , [ case Ctxt_fun_ty_out ctxt of None \<Rightarrow> OclTy_base_void | Some s \<Rightarrow> s ] ])
                      ([], D_ocl_HO_type env, l_isab_ty) in
              ( map_prod
                  (let env = env \<lparr> D_ocl_accessor := f_update_ocl (\<lambda> l. String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name # l) (D_ocl_accessor env) \<rparr> in
                   (\<lambda> D_ocl_HO_type. env \<lparr> D_ocl_HO_type := D_ocl_HO_type \<rparr>))
                  id
                  l
              , Consts_raw0
                  name
                  (ty_arrow (Typ_apply (Typ_base \<open>val\<close>) [Typ_base \<open>\<AA>\<close>, Typ_base \<open>'\<alpha>\<close>] # rev l_name))
                  (mk_dot attr_n var_at_when_ocl)
                  (Some (natural_of_nat (length (Ctxt_fun_ty_arg ctxt)))) # l_isab_const))
            [ (var_at_when_hol_post, var_at_when_ocl_post, update_D_ocl_accessor_post)
            , (var_at_when_hol_pre, var_at_when_ocl_pre, update_D_ocl_accessor_pre)])
      (Ctxt_clause ctxt)
      ((env, []), [])))"

definition "print_ctxt = (\<lambda>ctxt. (\<lambda>f x e. let (l, e) = f x e in bootstrap_floor l e)
  (\<lambda>l env.
    let ((env, l_isab_ty), l_isab) = print_ctxt_const ctxt env in
    (L.flatten [l_isab_ty, l_isab, l], env))
  [ META_all_meta_embedding (META_ctxt Floor2
      (map_invariant (\<lambda>T_inv b (OclProp_ctxt n p) \<Rightarrow>
                       T_inv b (OclProp_ctxt n (T_lambdas (Ctxt_param ctxt @@@@ [var_self]) p)))
                     (map_pre_post (\<lambda>pref ctxt. T_lambdas (make_ctxt_free_var pref ctxt))
                                   ctxt))) ])"

end
