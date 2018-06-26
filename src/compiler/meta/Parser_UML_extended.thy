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

section\<open>Instantiating the Parser of OCL (II)\<close>

theory  Parser_UML_extended
imports Meta_UML_extended
        "../../compiler_generic/meta_isabelle/Parser_init"
begin

subsection\<open>Building Recursors for Records\<close> (* NOTE part to be automated *)

definition "ocl_instance_single_rec0 f ocl = f
  (Inst_name ocl)
  (Inst_ty ocl)
  (Inst_attr_with ocl)
  (Inst_attr ocl)"

definition "ocl_instance_single_rec f ocl = ocl_instance_single_rec0 f ocl
  (ocl_instance_single.more ocl)"

(* *)

lemma [code]: "ocl_instance_single.extend = (\<lambda>ocl v. ocl_instance_single_rec0 (co4 (\<lambda>f. f v) ocl_instance_single_ext) ocl)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single.extend_def
                        co4_def K_def)
lemma [code]: "ocl_instance_single.make = co4 (\<lambda>f. f ()) ocl_instance_single_ext"
by(intro ext, simp add: ocl_instance_single.make_def
                        co4_def)
lemma [code]: "ocl_instance_single.truncate = ocl_instance_single_rec (co4 K ocl_instance_single.make)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single_rec_def
                        ocl_instance_single.truncate_def
                        ocl_instance_single.make_def
                        co4_def K_def)

subsection\<open>Main\<close>

context Parse
begin

definition "of_internal_oid a b = rec_internal_oid
  (ap1 a (b \<open>Oid\<close>) (of_nat a b))"

definition "of_internal_oids a b = rec_internal_oids
  (ap3 a (b \<open>Oids\<close>)
    (of_nat a b)
    (of_nat a b)
    (of_nat a b))"

definition "of_ocl_def_base a b = rec_ocl_def_base
  (ap1 a (b \<open>OclDefInteger\<close>) (of_string a b))
  (ap1 a (b \<open>OclDefReal\<close>) (of_pair a b (of_string a b) (of_string a b)))
  (ap1 a (b \<open>OclDefString\<close>) (of_string a b))"

definition "of_ocl_data_shallow a b = rec_ocl_data_shallow
  (ap1 a (b \<open>ShallB_term\<close>) (of_ocl_def_base a b))
  (ap1 a (b \<open>ShallB_str\<close>) (of_string a b))
  (ap1 a (b \<open>ShallB_self\<close>) (of_internal_oid a b))
  (ap1 a (b \<open>ShallB_list\<close>) (of_list a b snd))"

definition "of_ocl_list_attr a b f = (\<lambda>f0. co4 (\<lambda>f1. rec_ocl_list_attr f0 (\<lambda>s _ a rec. f1 s rec a)) (ap3 a))
  (ap1 a (b \<open>OclAttrNoCast\<close>) f)
  (b \<open>OclAttrCast\<close>)
    (of_string a b)
    id
    f"

definition "of_ocl_instance_single a b f = ocl_instance_single_rec
  (ap5 a (b (ext \<open>ocl_instance_single_ext\<close>))
    (of_option a b (of_string a b))
    (of_option a b (of_string a b))
    (of_option a b (of_string a b))
    (of_ocl_list_attr a b (of_list a b (of_pair a b (of_option a b (of_pair a b (of_string a b) (of_string a b))) (of_pair a b (of_string a b) (of_ocl_data_shallow a b)))))
    (f a b))"

definition "of_ocl_instance a b = rec_ocl_instance
  (ap1 a (b \<open>OclInstance\<close>)
    (of_list a b (of_ocl_instance_single a b (K of_unit))))"

definition "of_ocl_def_base_l a b = rec_ocl_def_base_l
  (ap1 a (b \<open>OclDefBase\<close>) (of_list a b (of_ocl_def_base a b)))"

definition "of_ocl_def_state_core a b f = rec_ocl_def_state_core
  (ap1 a (b \<open>OclDefCoreAdd\<close>) (of_ocl_instance_single a b (K of_unit)))
  (ap1 a (b \<open>OclDefCoreBinding\<close>) f)"

definition "of_ocl_def_state a b = rec_ocl_def_state
  (ap2 a (b \<open>OclDefSt\<close>) (of_string a b) (of_list a b (of_ocl_def_state_core a b (of_string a b))))"

definition "of_ocl_def_pp_core a b = rec_ocl_def_pp_core
  (ap1 a (b \<open>OclDefPPCoreAdd\<close>) (of_list a b (of_ocl_def_state_core a b (of_string a b))))
  (ap1 a (b \<open>OclDefPPCoreBinding\<close>) (of_string a b))"

definition "of_ocl_def_transition a b = rec_ocl_def_transition
  (ap3 a (b \<open>OclDefPP\<close>)
    (of_option a b (of_string a b))
    (of_ocl_def_pp_core a b)
    (of_option a b (of_ocl_def_pp_core a b)))"

definition "of_ocl_class_tree a b = rec_ocl_class_tree
  (ap2 a (b \<open>OclClassTree\<close>)
    (of_nat a b)
    (of_nat a b))"

end

lemmas [code] =
  Parse.of_internal_oid_def
  Parse.of_internal_oids_def
  Parse.of_ocl_def_base_def
  Parse.of_ocl_data_shallow_def
  Parse.of_ocl_list_attr_def
  Parse.of_ocl_instance_single_def
  Parse.of_ocl_instance_def
  Parse.of_ocl_def_base_l_def
  Parse.of_ocl_def_state_core_def
  Parse.of_ocl_def_state_def
  Parse.of_ocl_def_pp_core_def
  Parse.of_ocl_def_transition_def
  Parse.of_ocl_class_tree_def

end
