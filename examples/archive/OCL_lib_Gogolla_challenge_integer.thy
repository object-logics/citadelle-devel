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

chapter{* Gogolla's challenge on Sets *}

theory
  OCL_lib_Gogolla_challenge_integer
imports
  OCL_lib_Gogolla_challenge
begin

section{* Properties: OclIncluding *}
subsection{* Commutativity *}

lemma including_swap_ :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, int option option) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) \<doteq> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
by(rule including_swap__generic[OF assms])

lemma including_swap' : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) \<tau> = (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>)"
by simp

lemma including_swap : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) = (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
by simp

section{* Properties: (with comp fun commute) OclIncluding *}
subsection{* Preservation of comp fun commute (instance) *}

lemma including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, int option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
by(rule including_commute_generic)

lemma including_commute2 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
by(rule including_commute2_generic, simp_all add: assms)

lemma including_commute3 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x))"
by(rule including_commute3_generic, simp_all add: assms)

lemma including_commute4 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j))"
by(rule including_commute4_generic, simp_all add: assms)

lemma including_commute5 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i))"
by(rule including_commute5_generic, simp_all add: assms)

lemma including_commute6 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(x))"
by(rule including_commute6_generic, simp_all add: assms)

section{* Properties: (with comp fun commute) OclIterate and OclIncluding *}
subsection{* Identity *}

lemma i_including_id' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
   shows "(Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = S \<tau>"
by(rule i_including_id'_generic[OF including_commute], simp_all add: assms)

lemma iterate_including_id :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     shows "(S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j))) = S"
by(rule iterate_including_id_generic[OF including_commute], simp_all add: assms)

lemma i_including_id00 :
 assumes S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ((S :: ('\<AA>, int option option) Set) \<tau>)\<rceil>\<rceil>)"
   shows "\<And>\<tau>. \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a) ; set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x) in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set') = S')"
by(rule i_including_id00_generic[OF including_commute], simp_all add: assms)

lemma iterate_including_id00 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_incl : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
     shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=Set{} | r2->including\<^sub>S\<^sub>e\<^sub>t(j))) = S"
by(rule iterate_including_id00_generic[OF including_commute], simp_all add: assms)

subsection{* all defined (construction) *}

lemma preserved_defined :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: ('\<AA>, int option option) Set)"
   shows "let S' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> in
          \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A S')"
by(rule preserved_defined_generic[OF including_commute S_all_def], simp_all add: assms)

subsection{* Preservation of comp fun commute (main) *}

lemma iterate_including_commute_var :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. (F :: '\<AA> Integer
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). x, a} Set{\<lambda>(_:: '\<AA> st). x, a} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) =
                UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). y, a} Set{\<lambda>(_:: '\<AA> st). y, a} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
            \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (UML_Set.OclIterate (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) \<tau> =
                (UML_Set.OclIterate (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x) \<tau> "
     and a_int : "is_int a"
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. (((r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | F j r2))->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)))"
by(rule iterate_including_commute_var_generic, simp_all add: assms)

subsection{* Execution OclIncluding out of OclIterate (theorem) *}

lemma including_out1 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
by(rule including_out1_generic[OF including_commute including_commute2], simp_all add: assms)

lemma including_out2 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     and x0_int : "is_int x0"
     shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
 apply(rule including_out2_generic[OF including_commute including_commute2 including_commute3 including_commute4 including_commute5 including_out1])
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
by(rule preserved_defined, simp_all add: assms)

lemma including_out0 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_include : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
       and S_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
       and a_int : "is_int a"
     shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=Set{a} | acc->including\<^sub>S\<^sub>e\<^sub>t(x))) = (S->including\<^sub>S\<^sub>e\<^sub>t(a))"
by(rule including_out0_generic[OF including_commute], simp_all add: assms)

subsection{* Execution OclIncluding out of OclIterate (corollary) *}

lemma iterate_including_id_out :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
by(rule iterate_including_id_out_generic[OF including_commute including_commute2 including_commute3 including_out1], simp_all add: assms)

lemma iterate_including_id_out' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(a))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
by(rule iterate_including_id_out'_generic[OF including_commute including_out1], simp_all add: assms)

lemma iterate_including_id_out'''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(b))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
by(rule iterate_including_id_out''''_generic[OF including_out2 including_commute3 iterate_including_id_out], simp_all add: assms)

lemma iterate_including_id_out''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
by(rule iterate_including_id_out'''_generic[OF including_commute4 including_commute6 iterate_including_id_out''''], simp_all add: assms)

section{* Conclusion *}

lemma GogollasChallenge_on_sets:
      "\<tau> \<Turnstile> (Set{ \<six>,\<eight> } ->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1=Set{\<nine>}|
                        r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1|
                                    r2->including\<^sub>S\<^sub>e\<^sub>t(\<zero>)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)))) \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>}"
proof -
 have val_0 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<zero>" by simp
 have val_6 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<six>" by simp
 have val_8 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<eight>" by simp
 have val_9 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<nine>" by simp
 have OclInt0_int : "is_int \<zero>" by(simp add: is_int_def OclInt0_def)
 have OclInt6_int : "is_int \<six>" by(simp add: is_int_def OclInt6_def)
 have OclInt8_int : "is_int \<eight>" by(simp add: is_int_def OclInt8_def)
 have OclInt9_int : "is_int \<nine>" by(simp add: is_int_def OclInt9_def)
 show ?thesis
 by(rule GogollasChallenge_on_sets_generic[OF val_0 val_6 val_8 val_9 OclInt0_int OclInt6_int OclInt8_int OclInt9_int including_commute including_commute2 including_commute3 including_commute4 including_commute5 including_commute6 iterate_including_id iterate_including_id_out iterate_including_id_out' iterate_including_id_out''' iterate_including_id_out'''' iterate_including_commute_var including_out0 including_out1 including_out2])
qed

end
