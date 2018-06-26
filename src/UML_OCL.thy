(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
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

theory   UML_OCL
imports  "UML_Main"
         "../examples/archive/Monads" (* NOTE: perform lazily the extraction of generation_syntax
                                         so that dependencies can alternate among theories *)
         "compiler/Static"
         "compiler/Generator_dynamic_sequential"
begin

no_notation valid_SE (infix "\<Turnstile>" 15)
notation valid_SE (infix "\<Turnstile>\<^sub>M\<^sub>o\<^sub>n" 15)

definition "k x _ = \<lfloor>\<lfloor> x \<rfloor>\<rfloor>"
notation "k" ("\<guillemotleft>_\<guillemotright>")
lemma "K \<lfloor>\<lfloor>x\<rfloor>\<rfloor> = \<guillemotleft>x\<guillemotright>"
by(rule ext, simp add: K_def k_def)

(* Junk : TO BE DONE IN LIBRARY -- bu *)
(*<*)
lemma [simp]: "(\<guillemotleft>x\<guillemotright> <\<^sub>i\<^sub>n\<^sub>t \<guillemotleft>y\<guillemotright>) = \<guillemotleft>x < y\<guillemotright>"
by(rule ext, simp add: OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def k_def defined_def UML_Types.bot_fun_def
                       bot_option_def null_fun_def null_option_def)

lemma [simp]: "(\<guillemotleft>x\<guillemotright> \<le>\<^sub>i\<^sub>n\<^sub>t \<guillemotleft>y\<guillemotright>) = \<guillemotleft>x \<le> y\<guillemotright>"
by(rule ext, simp add: OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def k_def defined_def UML_Types.bot_fun_def
                       bot_option_def null_fun_def null_option_def)


lemma OclInt0' : "\<zero> = \<guillemotleft>0\<guillemotright>" by(rule ext, simp add: OclInt0_def k_def)
lemma OclInt1' : "\<one> = \<guillemotleft>1\<guillemotright>" by(rule ext, simp add: OclInt1_def k_def)
lemma OclInt2' : "\<two> = \<guillemotleft>2\<guillemotright>" by(rule ext, simp add: OclInt2_def k_def)
lemma OclInt3' : "\<three> = \<guillemotleft>3\<guillemotright>" by(rule ext, simp add: OclInt3_def k_def)
lemma OclInt4' : "\<four> = \<guillemotleft>4\<guillemotright>" by(rule ext, simp add: OclInt4_def k_def)
lemma OclInt5' : "\<five> = \<guillemotleft>5\<guillemotright>" by(rule ext, simp add: OclInt5_def k_def)
lemma OclInt6' : "\<six> = \<guillemotleft>6\<guillemotright>" by(rule ext, simp add: OclInt6_def k_def)
lemma OclInt7' : "\<seven> = \<guillemotleft>7\<guillemotright>" by(rule ext, simp add: OclInt7_def k_def)
lemma OclInt8' : "\<eight> = \<guillemotleft>8\<guillemotright>" by(rule ext, simp add: OclInt8_def k_def)
lemma OclInt9' : "\<nine> = \<guillemotleft>9\<guillemotright>" by(rule ext, simp add: OclInt9_def k_def)
lemma OclInt10': "\<one>\<zero>= \<guillemotleft>10\<guillemotright>"by(rule ext, simp add: OclInt10_def k_def)

lemma [simp]: "\<tau> \<Turnstile> \<guillemotleft>True\<guillemotright>"
              "\<tau> |\<noteq> \<guillemotleft>False\<guillemotright>"
by(simp add: OclValid_def true_def k_def)+
(*>*)

(*declare [[quick_and_dirty = true]]  shut up fully conservative mode *)

generation_syntax [ (*deep
                      (*(generation_semantics [ analysis (*, oid_start 10*) ])*)
                      (THEORY Model_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/Static"]
                               "../src/compiler/Generator_dynamic_sequential")
                      SECTION
                      (*SORRY*)
                      [ (*in OCaml module_name M*)
                        in self ]
                      (output_directory "../doc")
                  ,*) shallow (*SORRY*) ]

end