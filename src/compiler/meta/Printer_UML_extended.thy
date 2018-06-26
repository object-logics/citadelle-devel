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

section\<open>Instantiating the Printer for OCL (II)\<close>

theory  Printer_UML_extended
imports Meta_UML_extended
        Printer_UML
begin

context Print
begin

definition "To_oid = (\<lambda>Oid n \<Rightarrow> To_nat n)"

definition \<open>of_ocl_def_base = (\<lambda> OclDefInteger i \<Rightarrow> To_string i
                                | OclDefReal (i1, i2) \<Rightarrow> \<open>%s.%s\<close> (To_string i1) (To_string i2)
                                | OclDefString s \<Rightarrow> \<open>"%s"\<close> (To_string s))\<close>

fun of_ocl_data_shallow where
   "of_ocl_data_shallow e = (\<lambda> ShallB_term b \<Rightarrow> of_ocl_def_base b
                             | ShallB_str s \<Rightarrow> To_string s
                             | ShallB_self s \<Rightarrow> \<open>self %d\<close> (To_oid s)
                             | ShallB_list l \<Rightarrow> \<open>[ %s ]\<close> (String_concat \<open>, \<close> (List.map of_ocl_data_shallow l))) e"

fun of_ocl_list_attr where
   "of_ocl_list_attr f e = (\<lambda> OclAttrNoCast x \<Rightarrow> f x
                            | OclAttrCast ty (OclAttrNoCast x) _ \<Rightarrow> \<open>(%s :: %s)\<close> (f x) (To_string ty)
                            | OclAttrCast ty l _ \<Rightarrow> \<open>%s \<rightarrow> oclAsType( %s )\<close> (of_ocl_list_attr f l) (To_string ty)) e"

definition \<open>of_ocl_instance_single ocli =
 (let (s_left, s_right) =
    case Inst_name ocli of
      None \<Rightarrow> (case Inst_ty ocli of Some ty \<Rightarrow> (\<open>(\<close>, \<open> :: %s)\<close> (To_string ty)))
    | Some s \<Rightarrow>
        ( \<open>%s%s = \<close>
            (To_string s)
            (case Inst_ty ocli of None \<Rightarrow> \<open>\<close> | Some ty \<Rightarrow> \<open> :: %s\<close> (To_string ty))
        , \<open>\<close>) in
  \<open>%s%s%s\<close>
    s_left
    (of_ocl_list_attr
      (\<lambda>l. \<open>[ %s%s ]\<close>
             (case Inst_attr_with ocli of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> \<open>%s with_only \<close> (To_string s))
             (String_concat \<open>, \<close>
               (L.map (\<lambda>(pre_post, attr, v).
                            \<open>%s"%s" = %s\<close> (case pre_post of None \<Rightarrow> \<open>\<close>
                                                          | Some (s1, s2) \<Rightarrow> \<open>("%s", "%s") |= \<close> (To_string s1) (To_string s2))
                                          (To_string attr)
                                          (of_ocl_data_shallow v))
                         l)))
      (Inst_attr ocli))
    s_right)\<close>

definition "of_ocl_instance _ = (\<lambda> OclInstance l \<Rightarrow>
  \<open>Instance %s\<close> (String_concat \<open>
     and \<close> (L.map of_ocl_instance_single l)))"

definition "of_ocl_def_state_core l =
  String_concat \<open>, \<close> (L.map (\<lambda> OclDefCoreBinding s \<Rightarrow> To_string s
                             | OclDefCoreAdd ocli \<Rightarrow> of_ocl_instance_single ocli) l)"

definition "of_ocl_def_state _ (floor :: (* polymorphism weakening needed by code_reflect *)
                                         String.literal) = (\<lambda> OclDefSt n l \<Rightarrow>
  \<open>State%s %s = [ %s ]\<close>
    floor
    (To_string n)
    (of_ocl_def_state_core l))"

definition "of_ocl_def_pp_core = (\<lambda> OclDefPPCoreBinding s \<Rightarrow> To_string s
                                  | OclDefPPCoreAdd l \<Rightarrow> \<open>[ %s ]\<close> (of_ocl_def_state_core l))"

definition "of_ocl_def_transition _ (floor :: (* polymorphism weakening needed by code_reflect *)
                                            String.literal) = (\<lambda> OclDefPP n s_pre s_post \<Rightarrow>
  \<open>Transition%s %s%s%s\<close>
    floor
    (case n of None \<Rightarrow> \<open>\<close> | Some n \<Rightarrow> \<open>%s = \<close> (To_string n))
    (of_ocl_def_pp_core s_pre)
    (case s_post of None \<Rightarrow> \<open>\<close> | Some s_post \<Rightarrow> \<open> %s\<close> (of_ocl_def_pp_core s_post)))"

end

lemmas [code] =
  (* def *)
  Print.To_oid_def
  Print.of_ocl_def_base_def
  Print.of_ocl_instance_single_def
  Print.of_ocl_instance_def
  Print.of_ocl_def_state_core_def
  Print.of_ocl_def_state_def
  Print.of_ocl_def_pp_core_def
  Print.of_ocl_def_transition_def

  (* fun *)
  Print.of_ocl_list_attr.simps
  Print.of_ocl_data_shallow.simps

end
