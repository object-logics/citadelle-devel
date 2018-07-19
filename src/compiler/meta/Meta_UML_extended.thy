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

section\<open>OCL Meta-Model aka. AST definition of OCL (II)\<close>

theory  Meta_UML_extended
imports "../../compiler_generic/Init"
begin

subsection\<open>Type Definition\<close>

datatype internal_oid = Oid nat
datatype internal_oids = Oids nat \<comment> \<open>start\<close>
                              nat \<comment> \<open>oid for assoc (incremented from start)\<close>
                              nat \<comment> \<open>oid for inh (incremented from start)\<close>

datatype ocl_def_base = OclDefInteger "string" \<comment> \<open>integer digit\<close>
                      | OclDefReal "string \<comment> \<open>integer digit (left)\<close> \<times> string \<comment> \<open>integer digit (right)\<close>"
                      | OclDefString "string"

datatype ocl_data_shallow = ShallB_term ocl_def_base
                          | ShallB_str string \<comment> \<open>binding\<close>
                          | ShallB_self internal_oid
                          | ShallB_list "ocl_data_shallow list"

datatype 'a ocl_list_attr = OclAttrNoCast 'a \<comment> \<open>inh, own\<close>
                          | OclAttrCast
                              string \<comment> \<open>cast from\<close>
                              "'a ocl_list_attr" \<comment> \<open>cast entity\<close>
                              'a \<comment> \<open>inh, own\<close>

record ocl_instance_single = Inst_name :: "string option" \<comment> \<open>None: fresh name to be generated\<close>
                             Inst_ty :: "string option" \<comment> \<open>type\<close>
                             Inst_attr_with :: "string \<comment> \<open>name\<close> option"
                             Inst_attr :: "((  (string \<comment> \<open>pre state\<close> \<times> string \<comment> \<open>post state\<close>) option
                                               \<comment> \<open>state used when \<open>ocl_data_shallow\<close> is an object variable (for retrieving its oid)\<close>
                                             \<times> string \<comment> \<open>name\<close>
                                             \<times> ocl_data_shallow) list) \<comment> \<open>inh and own\<close>
                                           ocl_list_attr"

datatype ocl_instance = OclInstance "ocl_instance_single list" \<comment> \<open>mutual recursive\<close>

datatype ocl_def_base_l = OclDefBase "ocl_def_base list"

datatype 'a ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                               | OclDefCoreBinding 'a

datatype ocl_def_state = OclDefSt  string \<comment> \<open>name\<close>
                                  "string \<comment> \<open>name\<close> ocl_def_state_core list"

datatype ocl_def_pp_core = OclDefPPCoreAdd "string \<comment> \<open>name\<close> ocl_def_state_core list"
                         | OclDefPPCoreBinding string \<comment> \<open>name\<close>

datatype ocl_def_transition = OclDefPP
                              "string option" \<comment> \<open>None: fresh name to be generated\<close>
                              ocl_def_pp_core \<comment> \<open>pre\<close>
                              "ocl_def_pp_core option" \<comment> \<open>post\<close> \<comment> \<open>None: same as pre\<close>

datatype ocl_class_tree = OclClassTree nat \<comment> \<open>nb child\<close>
                                       nat \<comment> \<open>depth\<close>

subsection\<open>Object ID Management\<close>

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Succ n2) (Succ n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Succ n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitAll = (\<lambda>Oids n1 _ _ \<Rightarrow> Oids n1 n1 n1)"
definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"

subsection\<open>Operations of Fold, Map, ..., on the Meta-Model\<close>

definition "ocl_instance_single_empty =
  \<lparr> Inst_name = None, Inst_ty = None, Inst_attr_with = None, Inst_attr = OclAttrNoCast [] \<rparr>"

fun map_data_shallow_self where
   "map_data_shallow_self f e = (\<lambda> ShallB_self s \<Rightarrow> f s
                                 | ShallB_list l \<Rightarrow> ShallB_list (List.map (map_data_shallow_self f) l)
                                 | x \<Rightarrow> x) e"

fun map_list_attr where
   "map_list_attr f e =
     (\<lambda> OclAttrNoCast x \<Rightarrow> OclAttrNoCast (f x)
      | OclAttrCast c_from l_attr x \<Rightarrow> OclAttrCast c_from (map_list_attr f l_attr) (f x)) e"

definition "map_instance_single f ocli = ocli \<lparr> Inst_attr := map_list_attr (L.map f) (Inst_attr ocli) \<rparr>"

fun fold_list_attr where
   "fold_list_attr cast_from f l_attr accu = (case l_attr of
        OclAttrNoCast x \<Rightarrow> f cast_from x accu
      | OclAttrCast c_from l_attr x \<Rightarrow> fold_list_attr (Some c_from) f l_attr (f cast_from x accu))"

definition "inst_ty0 ocli = (case Inst_ty ocli of Some ty \<Rightarrow> Some ty
                                                | None \<Rightarrow> (case Inst_attr ocli of OclAttrCast ty _ _ \<Rightarrow> Some ty
                                                                                | _ \<Rightarrow> None))"
definition "inst_ty ocli = (case inst_ty0 ocli of Some ty \<Rightarrow> ty)"

definition "fold_instance_single f ocli = fold_list_attr (inst_ty0 ocli) (\<lambda> Some x \<Rightarrow> f x) (Inst_attr ocli)"
definition "fold_instance_single' f ocli = fold_list_attr (Inst_ty ocli) f (Inst_attr ocli)"

definition "str_of_def_base = (\<lambda> OclDefInteger _ \<Rightarrow> \<open>Integer\<close>
                               | OclDefReal _ \<Rightarrow> \<open>Real\<close>
                               | OclDefString _ \<Rightarrow> \<open>String\<close>)"

fun str_of_data_shallow where
   \<open>str_of_data_shallow e = (\<lambda> ShallB_term b \<Rightarrow> str_of_def_base b
                             | ShallB_str s \<Rightarrow> \<open>"\<close> @@ s @@ \<open>"\<close>
                             | ShallB_self _ \<Rightarrow> \<open>(*object_oid*)\<close>
                             | ShallB_list l \<Rightarrow> \<open>[ \<close> @@ String_concatWith \<open>, \<close> (List.map str_of_data_shallow l) @@ \<open> ]\<close>) e\<close>

definition "map_inst_single_self f =
  map_instance_single
    (map_prod id
      (map_prod id
        (map_data_shallow_self f)))"

end
