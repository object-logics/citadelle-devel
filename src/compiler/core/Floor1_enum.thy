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

section\<open>Main Translation for: Enumeration\<close>

theory  Floor1_enum
imports Core_init
begin

definition "print_enum = (\<lambda> OclEnum name_ty l \<Rightarrow> Pair
 (let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; option = Typ_apply_paren \<open>\<langle>\<close> \<open>\<rangle>\<^sub>\<bottom>\<close>
    ; name_ty_base = name_ty @@ String.isub \<open>base\<close>
    ; name_ty_base' = pref_generic_enum name_ty
    ; uu = \<open>'\<AA>\<close> in
  L.flatten
  [ [ O.datatype (Datatype' (pref_ty_enum name_ty) (L.map (\<lambda>constr. (pref_constr_enum constr, [])) l))
    , O.type_synonym (Type_synonym' name_ty_base (option (option (Typ_base (pref_ty_enum name_ty)))))
    , O.type_synonym (Type_synonym'' name_ty_base' [uu] (\<lambda> [u] \<Rightarrow> Typ_apply (Typ_base \<open>val\<close>) [Typ_base u, Typ_base name_ty_base]))
    , O.overloading
        (Overloading'
          (\<open>StrictRefEq\<close>)
          (Ty_arrow' (Typ_apply (Typ_base name_ty_base') [Typ_base uu]))
          (\<open>StrictRefEq\<close> @@ String.isub name_ty)
          (let var_x = \<open>x\<close>
             ; var_y = \<open>y\<close> in
           Term_rewrite
            (Term_rewrite (Term_annot (b var_x) (Typ_apply (Typ_base name_ty_base') [Typ_base uu])) \<open>\<doteq>\<close> (b var_y))
            \<open>\<equiv>\<close>
            (Term_lam \<open>\<tau>\<close>
              (\<lambda>var_tau.
                Term_if_then_else
                  (let f = \<lambda>v. Term_rewrite (Term_applys (a \<open>\<upsilon>\<close> (b v)) [b var_tau]) \<open>=\<close> (a \<open>true\<close> (b var_tau)) in
                   Term_binop (f var_x) \<open>\<and>\<close> (f var_y))
                  (Term_applys (Term_rewrite (b var_x) \<open>\<triangleq>\<close> (b var_y)) [b var_tau])
                  (a \<open>invalid\<close> (b var_tau)))))) ]
  , L.map
      (\<lambda>constr.
        O.definition
          (Definition (Term_rewrite (b constr)
                                    \<open>=\<close>
                                    (Term_lam \<open>_\<close> (\<lambda>_. Term_some (Term_some (Term_annot' (b (pref_constr_enum constr)) (pref_ty_enum name_ty)))))))) l ]))"

end
