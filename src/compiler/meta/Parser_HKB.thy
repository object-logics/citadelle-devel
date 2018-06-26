(******************************************************************************
 * Haskabelle --- Converting Haskell Source Files to Isabelle/HOL Theories.
 *                http://isabelle.in.tum.de/repos/haskabelle
 *
 * Copyright (c) 2007-2015 Technische Universität München, Germany
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

section\<open>Instantiating the Parser of Haskabelle\<close>

theory  Parser_HKB
imports Meta_HKB
        "../../compiler_generic/meta_isabelle/Parser_init"
begin

subsection\<open>Main\<close>

context Parse
begin

definition "of_ThyName a b = rec_ThyName
  (ap1 a (b \<open>ThyName\<close>) (of_string a b))"

definition "of_Name a b = rec_Name
  (ap2 a (b \<open>QName\<close>) (of_ThyName a b) (of_string a b))
  (ap1 a (b \<open>Name\<close>) (of_string a b))"

definition "of_Sort a b = of_list a b (of_Name a b)"

definition "of_Type a b = (\<lambda>f1 f2 f3. rec_Type f1 (\<lambda>_ _. f2) f3)
  (ap2 a (b \<open>Type\<close>) (of_Name a b) (of_list a b snd))
  (ar2 a (b \<open>Func\<close>) id)
  (ap1 a (b \<open>TVar\<close>) (of_Name a b))
  (b \<open>NoType\<close>)"

definition "of_Literal a b = rec_Literal
  (ap1 a (b \<open>Int\<close>) (of_nat a b))
  (ap1 a (b \<open>String\<close>) (of_string a b))"

definition "of_TLD_aux f_rec a b = (\<lambda>f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17. f_rec f1 f2 (co1 K f3) (\<lambda>_ _. f4) (\<lambda>_ _ _. f5) (\<lambda>l _. f6 (map (map_prod snd snd) l)) (\<lambda>_ l. f7 (map (map_prod snd snd) l)) (\<lambda>_ l. f8 (map snd l)) (\<lambda>a l. f9 a (map (map_prod id snd) l)) (K (f10 o map (map_prod id snd))) (\<lambda>a l. f11 a (map snd l)) (K f12) (f13 o map_prod snd snd) (K f14) (\<lambda>_ _. f15) (K f16) (f17 o map (map_prod snd snd)))
  (ap1 a (b \<open>Literal\<close>) (of_Literal a b))
  (ap1 a (b \<open>Const\<close>) (of_Name a b))
  (ar2 a (b \<open>Abs\<close>) (of_Name a b))
  (ar2 a (b \<open>App\<close>) id)
  (ar3 a (b \<open>If\<close>) id id)
  (ap2 a (b \<open>Let\<close>) (of_list a b (of_pair a b id id)) id)
  (ap2 a (b \<open>Case\<close>) (of_list a b (of_pair a b id id)) id)
  (ap2 a (b \<open>ListCompr\<close>) (of_list a b id) id)
  (ap2 a (b \<open>RecConstr\<close>) (of_Name a b) (of_list a b (of_pair a b (of_Name a b) id)))
  (ap2 a (b \<open>RecUpdate\<close>) (of_list a b (of_pair a b (of_Name a b) id)) id)
  (ap3 a (b \<open>DoBlock\<close>) (of_string a b) (of_list a b id) (of_string a b))
  (ar1 a (b \<open>Parenthesized\<close>))
  (* *)
  (ap1 a (b \<open>Generator\<close>) (of_pair a b id id))
  (ar1 a (b \<open>Guard\<close>))
  (* *)
  (ar2 a (b \<open>DoGenerator\<close>) id)
  (ar1 a (b \<open>DoQualifier\<close>))
  (ap1 a (b \<open>DoLetStmt\<close>) (of_list a b (of_pair a b id id)))"

definition "of_Term = of_TLD_aux rec_Term"
definition "of_ListComprFragment = of_TLD_aux rec_ListComprFragment"
definition "of_DoBlockFragment = of_TLD_aux rec_DoBlockFragment"

definition "of_Pat = of_Term"

definition "of_TypeSpec a b = rec_TypeSpec
  (ap2 a (b \<open>TypeSpec\<close>) (of_list a b (of_Name a b)) (of_Name a b))"

definition "of_TypeSign a b = rec_TypeSign
  (ap3 a (b \<open>TypeSign\<close>) (of_Name a b) (of_list a b (of_pair a b (of_Name a b) (of_Sort a b))) (of_Type a b))"

definition "of_Function_Kind b = rec_Function_Kind
  (b \<open>Definition\<close>)
  (b \<open>Primrec\<close>)
  (b \<open>Fun\<close>)
  (b \<open>Function_Sorry\<close>)"

definition "of_Function_Stmt a b = rec_Function_Stmt
  (ap3 a (b \<open>Function_Stmt\<close>) (of_Function_Kind b) (of_list a b (of_TypeSign a b)) (of_list a b (of_pair a b (of_pair a b (of_Name a b) (of_list a b (of_Pat a b))) (of_Term a b))))"

definition "of_Stmt a b = rec_Stmt
  (ap1 a (b \<open>Datatype\<close>) (of_list a b (of_pair a b (of_TypeSpec a b) (of_list a b (of_pair a b (of_Name a b) (of_list a b (of_Type a b)))))))
  (ap2 a (b \<open>Record\<close>) (of_TypeSpec a b) (of_list a b (of_pair a b (of_Name a b) (of_Type a b))))
  (ap1 a (b \<open>TypeSynonym\<close>) (of_list a b (of_pair a b (of_TypeSpec a b) (of_Type a b))))
  (ap1 a (b \<open>Function\<close>) (of_Function_Stmt a b))
  (ap3 a (b \<open>Class\<close>) (of_Name a b) (of_list a b (of_Name a b)) (of_list a b (of_TypeSign a b)))
  (ap4 a (b \<open>Instance\<close>) (of_Name a b) (of_Name a b) (of_list a b (of_pair a b (of_Name a b) (of_Sort a b))) (of_list a b (of_Function_Stmt a b)))
  (ap1 a (b \<open>Comment\<close>) (of_string a b))
  (ap1 a (b \<open>SML\<close>) (of_Function_Stmt a b))"

definition "of_Module a b = rec_Module
  (ap4 a (b \<open>Module\<close>) (of_ThyName a b) (of_list a b (of_ThyName a b)) (of_list a b (of_Stmt a b)) (of_bool b))"

definition "of_IsaUnit a b = rec_IsaUnit
  (ap4 a (b \<open>IsaUnit\<close>) (of_pair a b (of_bool b) (of_nat a b)) (of_list a b (of_pair a b (of_string a b) (of_option a b (of_string a b)))) (of_string a b) (of_pair a b (of_list a b (of_Module a b)) (of_bool b)))"

end

lemmas [code] =
  Parse.of_ThyName_def
  Parse.of_Name_def
  Parse.of_Sort_def
  Parse.of_Type_def
  Parse.of_Literal_def
  Parse.of_TLD_aux_def
  Parse.of_Term_def
  Parse.of_ListComprFragment_def
  Parse.of_DoBlockFragment_def
  Parse.of_Pat_def
  Parse.of_TypeSpec_def
  Parse.of_TypeSign_def
  Parse.of_Function_Kind_def
  Parse.of_Function_Stmt_def
  Parse.of_Stmt_def
  Parse.of_Module_def
  Parse.of_IsaUnit_def

end
