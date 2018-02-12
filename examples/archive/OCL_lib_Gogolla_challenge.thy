(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib_Gogolla_challenge.thy --- Example using the OCL library.
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
  OCL_lib_Gogolla_challenge
imports
  "../../src/UML_Library"
  Isabelle_Finite_Set
begin

no_notation None ("\<bottom>")

(*
Sequence{6,8}->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1:Sequence(Integer)=Sequence{9}|
  r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2:Sequence(Integer)=r1|
    r2->including\<^sub>S\<^sub>e\<^sub>t(0)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)))
*)
text{* In this section we normalize the following ground OCL term:
@{term "Set{\<six>,\<eight>}->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1=Set{\<nine>}|
  r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1|
    r2->including\<^sub>S\<^sub>e\<^sub>t(\<zero>)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)))"}.
Starting from a set of numbers, this complex expression finally involves only two combinators:
 \<^enum> @{const UML_Set.OclIterate}, and
 \<^enum> @{const UML_Set.OclIncluding}.

As there is no removing, we conjecture that the final result should be equal to the set
containing all ground numbers appearing in the expression, namely @{term \<six>}, @{term \<eight>}, @{term \<nine>}, and @{term \<zero>}. *}
(* text{*(modulo ordering and duplication for sequences)*} *)

text{* The following part sets up the necessary requirement so that one can ideally normalize
a general term composed of a set of numbers applied to an arbitrary nesting of
@{term OclIterate} and @{term OclIncluding}.
Instead of following a particular conventional strategy (e.g., call by value, by need, ...),
for efficiency reasons, we present in the next subsections some algebraic properties on sets
to manually minimize the number of reduction steps before obtaining a normal form. *}

section{* Introduction *}

text{* Besides the @{term invalid} and @{term null} exception elements, the other concept that
could be treated as a kind of monadic exception is the finiteness property of OCL sets.
Since the iteration operation can only be performed on finite sets, the definition of @{term OclIterate}
contains as prerequisite a check that the given argument is finite. If it is the case,
@{term Finite_Set.fold} is then called internally to execute the iteration. *}

text{* We intend to provide a generic solution to the Gogolla's challenge,
in the sense that we focus on an arbitrary list of nested @{term OclIterate} combinators.
A naive approach for simplifying such huge expression would be to repeatedly rewrite with
@{thm[source] UML_Set.OclIterate_including}.
However, @{thm[source] UML_Set.OclIterate_including} contains @{term "comp_fun_commute F"} as hypothesis
and in case @{term "F"} is again a nested operation on OCL sets, we would still need additional assumptions
in order to further prove that @{term "comp_fun_commute F"} is true (like the
validity, definedness and finiteness properties,
and the finiteness is precisely required for all sets occurring
in a chain of @{term OclIterate} nested term).
As illustration, @{file "OCL_lib_Gogolla_challenge_naive.thy"} contains additional several lemmas
that can be proved but will not be used,
since they have @{term "comp_fun_commute F"} as hypothesis. *}

text{* As solution, we propose now to write an Isabelle locale similar as the locale @{term "comp_fun_commute"}
but containing the additional properties that sets should fulfill
while traveling through the nested @{term OclIterate}.
For reusability, these properties will be abstractly regrouped in @{term "is_int"} (representing ground value in a set, like integer)
and @{term "all_defined"} (representing ground sets). *}

section{* Properties: mtSet *}

lemma mtSet_all_def : "all_defined \<tau> Set{}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 show ?thesis
  apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse B)
 by (metis (no_types) foundation16 mtSet_def mtSet_defined transform1)
qed

lemma cp_mtSet : "\<And>x. Set{} = (\<lambda>_. Set{} x)"
by (metis (hide_lams, no_types) mtSet_def)

section{* Properties: OclIncluding *}

subsection{* Identity *}

lemma including_id'' : "\<tau> \<Turnstile> \<delta> (S:: ('\<AA>, 'a option option) Set) \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x) \<tau> = S \<tau>"
 apply(simp add: UML_Set.OclIncluding_def OclValid_def insert_absorb abs_rep_simp' del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
by (metis (no_types) OclValid_def Set_inv_lemma foundation18')

lemma including_id' : "all_defined \<tau> (S:: ('\<AA>, 'a option option) Set) \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x) \<tau> = S \<tau>"
by(rule including_id'', (simp add: all_defined_def)+)

lemma including_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
   shows "            \<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x) = S"
by(rule, rule including_id', simp add: S_all_def, blast)

subsection{* Commutativity *}

lemma including_swap__generic :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a::null) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) \<doteq> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 apply(simp only: OclIncluding_commute StrictRefEq\<^sub>S\<^sub>e\<^sub>t.refl_ext)
by (metis "UML_Set.OclIncluding.1" OclIf_true' OclIncluding_valid_args_valid OclValid_def S_def i_val j_val)

subsection{* Congruence *}

lemma including_subst_set : "(s::('\<AA>,'a::null)Set) = t \<Longrightarrow> s->including\<^sub>S\<^sub>e\<^sub>t(x) = (t->including\<^sub>S\<^sub>e\<^sub>t(x))"
by(simp)

lemmas including_subst_set' = OclIncluding_cong'

lemma including_subst_set'' : "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> (s::('\<AA>,'a::null)Set) \<tau> = t \<tau> \<Longrightarrow> s->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau> = (t->including\<^sub>S\<^sub>e\<^sub>t(x)) \<tau>"
 apply(frule including_subst_set'[where s = s and t = t and x = x], simp_all del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 apply (metis (hide_lams, no_types) OclValid_def foundation20 foundation22)
by (metis UML_Set.OclIncluding.cp0)


subsection{* all defined (construction) *}

lemma cons_all_def' :
  assumes S_all_def : "all_defined \<tau> S"
  assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> (S->including\<^sub>S\<^sub>e\<^sub>t(x))"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

 have G1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1] x_val A Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject B C OclValid_def Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_cases Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def insert_compr insert_def not_Some_eq null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)
  done

 have G2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1] x_val A Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject B C OclValid_def Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_cases Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def insert_compr insert_def not_Some_eq null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)
  done

 have G : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def G1 G2)
  done

 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def UML_Set.OclIncluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF invert_all_defined_aux]
                S_all_def[simplified all_defined_def]
                x_val, simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<union> {x \<tau>}\<rfloor>\<rfloor> else invalid \<tau>"])
   apply(simp add: all_defined_set'_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

lemma cons_all_def:
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> S->including\<^sub>S\<^sub>e\<^sub>t(x)"
by(rule cons_all_def', simp_all add: assms)

subsection{* all defined (inversion) *}

lemma invert_all_defined : "all_defined \<tau> (S->including\<^sub>S\<^sub>e\<^sub>t(x)) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> S"
 proof -
 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

 have OclIncluding_finite_rep_set : "\<And>\<tau> X x. \<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  apply(rule OclIncluding_finite_rep_set)
  apply(metis OclValid_def foundation5)+
 done

  show "all_defined \<tau> (S->including\<^sub>S\<^sub>e\<^sub>t(x)) \<Longrightarrow> ?thesis"
   apply(simp add: all_defined_def all_defined_set'_def)
   apply(erule conjE, frule OclIncluding_finite_rep_set[of \<tau> S x], simp)
  by (metis foundation5)
qed

lemma invert_all_defined' : "(\<forall>\<tau>. all_defined \<tau> (S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x))) \<Longrightarrow> is_int (\<lambda> (_:: '\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> S)"
   apply(rule conjI)
   apply(simp only: is_int_def, rule allI)
   apply(erule_tac x = \<tau> in allE, simp)
   apply(drule invert_all_defined, simp)
   apply(rule allI)
   apply(erule_tac x = \<tau> in allE)
   apply(drule invert_all_defined, simp)
done

subsection{* Preservation of cp *}

lemma including_cp_gen : "cp f \<Longrightarrow> cp (\<lambda>r2. ((f r2)->including\<^sub>S\<^sub>e\<^sub>t(x)))"
 apply(unfold cp_def)
 apply(subst UML_Set.OclIncluding.cp0[of _ x])
 apply(drule exE) prefer 2 apply assumption
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. fa X_\<tau> \<tau>)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. x \<tau>)) \<tau>" in exI, simp)
done

lemma including_cp : "cp (\<lambda>r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(x)))"
by(rule including_cp_gen, simp)

lemma including_cp' : "cp (UML_Set.OclIncluding S)"
 apply(unfold cp_def)
 apply(subst UML_Set.OclIncluding.cp0)
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. S \<tau>)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. X_\<tau>)) \<tau>" in exI, simp)
done

lemma including_cp''' : "cp (UML_Set.OclIncluding S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j))"
by(rule including_cp')

lemma including_cp2 : "cp (\<lambda>r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(y))"
by(rule including_cp_gen, simp add: including_cp)

lemma including_cp3 : "cp (\<lambda>r2. ((r2->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(y))->including\<^sub>S\<^sub>e\<^sub>t(z))"
by(rule including_cp_gen, simp add: including_cp2)

subsection{* Preservation of global judgment *}

lemma including_cp_all :
 assumes x_int : "is_int x"
     and S_def : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> S"
     and S_incl : "S \<tau>1 = S \<tau>2"
   shows  "S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>1 = S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>2"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(unfold UML_Set.OclIncluding_def)
  apply(simp add:  S_def[simplified OclValid_def] int_is_valid[OF x_int, simplified OclValid_def] S_incl)
  apply(subgoal_tac "x \<tau>1 = x \<tau>2", simp)
  apply(insert x_int[simplified is_int_def, THEN spec, of \<tau>1, THEN conjunct2, THEN spec], simp)
 done
qed

subsection{* Preservation of non-emptiness *}

lemma including_notempty :
  assumes S_def : "\<tau> \<Turnstile> \<delta> S"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
      and S_notempty : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
    shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show ?thesis
  apply(unfold UML_Set.OclIncluding_def)
  apply(simp add: S_def[simplified OclValid_def] x_val[simplified OclValid_def] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF insert_in_Set_0[OF S_def x_val]])
 done
qed

lemma including_notempty' :
  assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Set{x} \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have insert_in_Set_0 : "\<And>S \<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show ?thesis
  apply(unfold UML_Set.OclIncluding_def)
  apply(simp add: x_val[simplified OclValid_def])
  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
  apply(rule insert_in_Set_0)
  apply(simp add: mtSet_all_def)
  apply(simp_all add: x_val)
 done
qed

section{* Properties: Constant set *}

lemma cp_singleton : "(\<lambda>_. Set{\<lambda>(_:: '\<AA> st). x} \<tau>) = Set{\<lambda>(_:: '\<AA> st). x}"
 apply(rule ext, rename_tac \<tau>')
 apply(subst const_OclIncluding[simplified const_def], simp)
by(simp add: mtSet_def, simp)

lemma cp_doubleton :
 assumes a_int : "const a"
   shows "(\<lambda>_. Set{\<lambda>(_:: '\<AA> st). x, a} \<tau>) = Set{\<lambda>(_:: '\<AA> st). x, a}"
 apply(rule ext, rename_tac \<tau>')
 apply(rule const_OclIncluding[simplified const_def, THEN spec, THEN spec], simp)
 apply(intro allI, rule const_OclIncluding[simplified const_def, THEN spec, THEN spec])
 apply(simp add: a_int[simplified const_def])
by(simp add: mtSet_def)

lemma flatten_int : "Set{a,a} = Set{a}"
by simp

section{* Properties: OclExcluding *}
subsection{* Identity *}

lemma excluding_id'': "\<tau> \<Turnstile> \<delta> (S:: ('\<AA>, 'a option option) Set) \<Longrightarrow>
                       \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. x) \<Longrightarrow>
                       x \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       S->excluding\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x) \<tau> = S \<tau>"
by(simp add: UML_Set.OclExcluding_def OclValid_def abs_rep_simp')

lemma excluding_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and x_int : "is_int (\<lambda>(\<tau>:: '\<AA> st). x)"
   shows "            \<forall>\<tau>. x \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->excluding\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x) = S"
by(rule, rule excluding_id'',
   simp add: S_all_def[simplified all_defined_def], simp add: int_is_valid[OF x_int], blast)

subsection{* all defined (construction) *}

lemma cons_all_def_e :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> S->excluding\<^sub>S\<^sub>e\<^sub>t(x)"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  qed

 have G1 : "\<And>\<tau>. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C[of \<tau>], simp)
          apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def)
  done
 qed

 have G2 : "\<And>\<tau>. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C[of \<tau>], simp)
          apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  done
 qed

 have G : "\<And>\<tau>. (\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def G1 G2)
  done
 qed

 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def UML_Set.OclExcluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF invert_all_defined_aux]
                S_all_def[simplified all_defined_def, of \<tau>]
                x_val[of \<tau>], simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor>"])
   apply(simp add: all_defined_set'_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

subsection{* Execution *}

lemma excluding_unfold' :
  assumes S_all_def : "\<tau> \<Turnstile> \<delta> S"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}"
proof -
 have C : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert S_all_def x_val, frule Set_inv_lemma)
          by(simp add: foundation18 invalid_def)
 show ?thesis
 by(simp add: UML_Set.OclExcluding_def S_all_def[simplified OclValid_def] x_val[simplified OclValid_def] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C])
qed

lemma excluding_unfold :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
      and x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}"
by(rule excluding_unfold', simp add: S_all_def[simplified all_defined_def], simp add: x_val)

section{* Properties: OclIncluding and OclExcluding *}
subsection{* Identity *}

lemma Ocl_insert_Diff' :
 assumes S_all_def : "\<tau> \<Turnstile> \<delta> (S :: ('\<AA>, 'a option option) Set)"
     and x_mem : "x \<in> (\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
     and x_int : "\<tau> \<Turnstile> \<upsilon> x"
   shows "S->excluding\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau> = S \<tau>"
proof -
 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: foundation18 invalid_def)
 done
 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)
 have x_mem : "x \<tau> \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
 by(rule inj_image_mem_iff[OF inject, THEN iffD1], insert x_mem, fast)
 show ?thesis
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> (S->excluding\<^sub>S\<^sub>e\<^sub>t(x))")
   prefer 2
   apply(simp add: foundation10 S_all_def x_int)
  apply(simp add: UML_Set.OclExcluding_def UML_Set.OclIncluding_def S_all_def[simplified OclValid_def] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF remove_in_Set_0] x_int[simplified OclValid_def] OclValid_def)
  apply(insert x_mem, drule insert_Diff[symmetric], simp)
 by(subst abs_rep_simp', simp add: S_all_def[simplified all_defined_def], simp)
qed

lemma Ocl_insert_Diff :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and x_mem : "\<And>\<tau>. x \<in> (\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
     and x_int : "is_int x"
   shows "S->excluding\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(x) = S"
 apply(rule ext, rename_tac \<tau>)
 apply(rule Ocl_insert_Diff', simp add: S_all_def[simplified all_defined_def], insert x_mem, fast)
by(simp add: int_is_valid[OF x_int])

section{* Properties: OclIterate *}

subsection{* all defined (inversion) *}

lemma i_invert_all_defined_not :
 assumes A_all_def : "\<exists>\<tau>. \<not> all_defined \<tau> S"
   shows "\<exists>\<tau>. \<not> all_defined \<tau> (UML_Set.OclIterate S S F)"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 show ?thesis
  apply(insert A_all_def)
  apply(drule exE) prefer 2 apply assumption
  apply(rule_tac x = \<tau> in exI)
  proof - fix \<tau> show "\<not> all_defined \<tau> S \<Longrightarrow> \<not> all_defined \<tau> (UML_Set.OclIterate S S F)"
   apply(unfold UML_Set.OclIterate_def)
   apply(case_tac "\<tau> \<Turnstile> (\<delta> S) \<and> \<tau> \<Turnstile> (\<upsilon> S) \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp add: OclValid_def all_defined_def)
   apply(simp add: all_defined_set'_def)
   apply(simp add: all_defined_def all_defined_set'_def defined_def OclValid_def false_def true_def bot_fun_def)
  done
 qed
qed

lemma i_invert_all_defined :
 assumes A_all_def : "\<And>\<tau>. all_defined \<tau> (UML_Set.OclIterate S S F)"
   shows "all_defined \<tau> S"
by (metis A_all_def i_invert_all_defined_not)

lemma i_invert_all_defined' :
 assumes A_all_def : "\<forall>\<tau>. all_defined \<tau> (UML_Set.OclIterate S S F)"
   shows "\<forall>\<tau>. all_defined \<tau> S"
by (metis A_all_def i_invert_all_defined)

section{* Properties: (with comp fun commute) invalid *}
subsection{* Preservation of comp fun commute (main) *}

lemma bot_commute : "comp_fun_commute (\<lambda>_ _. \<bottom>)"
by(simp add: comp_fun_commute_def)

section{* Properties: (with comp fun commute) OclIf *}
subsection{* Preservation of comp fun commute (main) *}

lemma if_commute_gen_var_gen :
  assumes f_comm : "comp_fun_commute f"
  assumes F_comm : "comp_fun_commute F"
      and F_cp : "\<And>x S \<tau>. F x S \<tau> = F x (\<lambda>_. S \<tau>) \<tau>"
      and f_cp : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
      and F_strict : "\<And>x. F x invalid = invalid"
      and f_strict : "\<And>x. f x invalid = invalid"
      and comm : "\<And>x y S \<tau>. F y (f x S) \<tau> = f x (F y S) \<tau>"
    shows "comp_fun_commute (\<lambda>j r2. if c j then (F j r2) else f j r2 endif)"
proof -
 have F_comm : "\<And>y x S. (F y (F x S)) = (F x (F y S))"
 by (metis comp_fun_commute.fun_left_comm F_comm)

 have f_comm : "\<And>y x S. (f y (f x S)) = (f x (f y S))"
 by (metis comp_fun_commute.fun_left_comm f_comm)

 have if_id : "\<And>x. (if x then invalid else invalid endif) = invalid"
 by(rule ext,simp add: OclIf_def)

 show ?thesis
  apply(simp add: comp_fun_commute_def comp_def)
  apply(rule allI)+
  apply(rule ext, rename_tac S)
  apply(rule ext, rename_tac \<tau>)
  proof - fix y x S \<tau> show "(if c y then F y (if c x then F x S else f x S endif) else f y (if c x then F x S else f x S endif) endif) \<tau> =
                            (if c x then F x (if c y then F y S else f y S endif) else f x (if c y then F y S else f y S endif) endif) \<tau>"
   apply(subst (1 2) cp_OclIf, subst (1 2) F_cp, subst (1 2) f_cp, subst (1 2 4 5) cp_OclIf)
   apply(cut_tac bool_split_0[where X = "c y" and \<tau> = \<tau>], auto)
   apply(simp_all add: cp_OclIf[symmetric] F_cp[symmetric] f_cp[symmetric] F_strict f_strict if_id)
   (* *)
   apply(subst F_cp, subst (1 2) cp_OclIf)
   apply(cut_tac bool_split_0[where X = "c x" and \<tau> = \<tau>], auto)
   apply(simp_all add: cp_OclIf[symmetric] F_cp[symmetric] f_cp[symmetric] F_strict f_strict if_id F_comm comm)
   (* *)
   apply(subst f_cp, subst (1 2) cp_OclIf)
   apply(cut_tac bool_split_0[where X = "c x" and \<tau> = \<tau>], auto)
   apply(simp_all add: cp_OclIf[symmetric] F_cp[symmetric] f_cp[symmetric] F_strict f_strict if_id f_comm comm)
  done
 qed
qed

section{* Properties: (with comp fun commute) OclIncluding *}
subsection{* Preservation of comp fun commute (main) *}

lemma including_commute_gen_var_gen :
  assumes f_comm : "comp_fun_commute F"
      and f_out : "\<And>x y S \<tau>. F x (S->including\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = (F x S)->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau>"
    shows "comp_fun_commute (\<lambda>j r2. ((F j r2)->including\<^sub>S\<^sub>e\<^sub>t(a)))"
proof -
 have comm : "\<And>y x S. (F y (F x S)) = (F x (F y S))"
 by (metis comp_fun_commute.fun_left_comm f_comm)
 show ?thesis
  apply(simp add: comp_fun_commute_def comp_def)
  apply(rule allI)+
  apply(rule ext, rename_tac S)
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst f_out)
  apply(subst comm)
  apply(subst f_out[symmetric], simp)
 done
qed

lemma including_commute_gen_var :
  assumes f_comm : "EQ_comp_fun_commute F"
      and f_out : "\<And>x y S \<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> F x (S->including\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = (F x S)->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau>"
      and a_int : "is_int a"
    shows "EQ_comp_fun_commute (\<lambda>j r2. ((F j r2)->including\<^sub>S\<^sub>e\<^sub>t(a)))"
proof -
 interpret EQ_comp_fun_commute F by (rule f_comm)

 have f_cp : "\<And>x y \<tau>. F x y \<tau> = F (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>) \<tau>"
 by (metis F_cp F_cp_set)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def)
  apply(rule conjI)+
  apply(rule allI)+

  proof - fix x S \<tau> show "(F x S)->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau> = (F (\<lambda>_. x \<tau>) S)->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
  by(subst (1 2) UML_Set.OclIncluding.cp0, subst F_cp, simp)

  apply_end(rule conjI)+ apply_end(rule allI)+

  fix x S \<tau> show "(F x S)->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau> = (F x (\<lambda>_. S \<tau>))->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
  by(subst (1 2) UML_Set.OclIncluding.cp0, subst F_cp_set, simp)

  apply_end(rule allI)+ apply_end(rule impI)+

  fix x fix S fix \<tau>1 \<tau>2
  show "is_int x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> ((F x S)->including\<^sub>S\<^sub>e\<^sub>t(a)) \<tau>1 = ((F x S)->including\<^sub>S\<^sub>e\<^sub>t(a)) \<tau>2"
   apply(subgoal_tac "x \<tau>1 = x \<tau>2") prefer 2 apply (simp add: is_int_def) apply(metis surj_pair)
   apply(subgoal_tac "\<And>\<tau>. all_defined \<tau> (F x S)") prefer 2 apply(rule all_def[THEN iffD2], simp only: int_is_valid)
   apply(subst including_cp_all[of _ _ \<tau>1 \<tau>2]) apply(simp add: a_int) apply(rule all_defined1, blast)
   apply(rule cp_gen, simp, blast, simp)
   apply(simp)
  done
  apply_end(rule conjI)
  apply_end(rule allI)+ apply_end(rule impI)+

  apply_end(rule including_notempty)
  apply_end(rule all_defined1)
  apply_end(simp add: all_def, metis surj_pair, simp)
  apply_end(simp add: int_is_valid[OF a_int])
  apply_end(rule notempty, blast, simp, simp)

  apply_end(rule conjI) apply_end(rule allI)+
  apply_end(rule iffI)
  apply_end(drule invert_all_defined, simp add: all_def)
  apply_end(rule cons_all_def', simp add: all_def)
  apply_end(simp add: int_is_valid[OF a_int])

  apply_end(rule allI)+ apply_end(rule impI)+

  fix x y S \<tau> show "\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> all_defined \<tau> S \<Longrightarrow>
  (F y ((F x S)->including\<^sub>S\<^sub>e\<^sub>t(a)))->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau> =
  (F x ((F y S)->including\<^sub>S\<^sub>e\<^sub>t(a)))->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
   apply(rule including_subst_set'')
   apply(rule all_defined1)
   apply(simp add: all_def, rule cons_all_def', simp add: all_def)
   apply(simp add: int_is_valid[OF a_int])
   apply(rule all_defined1)
   apply(simp add: all_def, rule cons_all_def', simp add: all_def)
   apply(simp add: int_is_valid[OF a_int])+
   apply(subst f_out)
   apply(rule all_defined1, simp add: all_def, simp)
   apply(simp add: int_is_valid[OF a_int])
   apply(subst UML_Set.OclIncluding.cp0)
   apply(subst commute, simp_all add: UML_Set.OclIncluding.cp0[symmetric] f_out[symmetric])
   apply(subst f_out[symmetric])
   apply(rule all_defined1, simp add: all_def, simp)
   apply(simp add: int_is_valid[OF a_int])
   apply(simp)
  done
 qed
qed

subsection{* Preservation of comp fun commute (instance) *}

lemma including_commute0_generic :
 shows  "comp_fun_commute (\<lambda>j (r2:: ('\<AA>, 'a option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
by(simp add: comp_fun_commute_def comp_def)

lemma including_commute_generic :
 shows  "EQ_comp_fun_commute (\<lambda>j (r2:: ('\<AA>, 'a option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp including_cp')
  apply(rule conjI, rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, simp) apply(rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+
  apply(rule impI)+ apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp) apply(simp)
 by (metis OclIncluding_commute cons_all_def' invert_all_defined)
qed

lemma including_commute2_generic :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 apply(rule including_commute_gen_var)
 apply(rule including_commute_generic, simp_all add: i_int)
done

lemma including_commute3_generic :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp2 including_cp')
  apply(rule conjI, rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, simp) apply(rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, subst (1 3) UML_Set.OclIncluding.cp0, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) using all_defined1 cons_all_def' i_int int_is_valid apply blast
  apply(rule including_cp_all) apply(simp add: i_int) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule impI)+
  apply(rule including_notempty) using all_defined1 cons_all_def' i_int int_is_valid apply blast apply(simp)
  apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp add: i_val) apply(simp)
 by (metis OclIncluding_commute cons_all_def' i_val invert_all_defined)
qed

lemma including_commute4_generic :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(rule including_commute_gen_var)
  apply(rule including_commute3_generic)
  apply(simp_all add: i_int j_int)
 done
qed

lemma including_commute5_generic :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(rule including_commute_gen_var)+
  apply(simp add: including_commute_generic)
  apply(simp_all add: i_int j_int)
 done
qed

lemma including_commute6_generic :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp3 including_cp''')
  apply(rule conjI, rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, simp)
  apply(rule conjI) apply(subst (1 2) UML_Set.OclIncluding.cp0, subst (1 3) UML_Set.OclIncluding.cp0, subst (1 4) UML_Set.OclIncluding.cp0, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val j_val)
  apply(rule including_cp_all) apply(simp) apply(simp add: j_int)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val)
  apply(rule including_cp_all) apply(simp) apply(simp add: i_int) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule impI)+
  apply(rule including_notempty)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val j_val) apply(simp)
  apply(rule including_notempty)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val)  apply(simp add: j_val)
  apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp add: i_val) apply(simp)
 by (metis (no_types, hide_lams) OclIncluding_commute cons_all_def' i_val invert_all_defined j_val)
qed

section{* Properties: (with comp fun commute) OclIterate *}
subsection{* Congruence *}

lemma iterate_subst_set_rec :
 assumes A_defined : "\<forall>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
   shows "let Fa' = (\<lambda>a \<tau>. a) ` Fa
                    ; x' = \<lambda>\<tau>. x in
           x \<notin> Fa \<longrightarrow>
           all_int_set (insert x' Fa') \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A Fa')) \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A (insert x' Fa')))"
 apply(simp only: Let_def) apply(rule impI)+ apply(rule allI)+
 apply(rule EQ_comp_fun_commute000.all_defined_fold_rec[OF F_commute[THEN c0_of_c, THEN c000_of_c0]], simp add: A_defined, simp, simp, blast)
done

lemma iterate_subst_set_rec0 :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F:: ('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
   shows "
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A (insert x Fa))"
 apply(rule allI, rule EQ_comp_fun_commute0.all_defined_fold_rec[OF F_commute])
 apply(simp, simp, simp add: all_int_set_def all_defined_set_def is_int_def, blast)
done

lemma iterate_subst_set_rec0' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. (F:: ('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). \<lfloor>a\<rfloor>) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A (insert x Fa))"
 apply(rule allI, rule EQ_comp_fun_commute0'.all_defined_fold_rec[OF F_commute])
 apply(simp, simp, simp add: all_int_set_def all_defined_set'_def is_int_def, blast)
done

lemma iterate_subst_set_gen :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<Longrightarrow> F x acc = G x acc"
     and P0 : "P A"
     and Prec : "\<And>x Fa. all_int_set Fa \<Longrightarrow>
             is_int x \<Longrightarrow> x \<notin> Fa \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A Fa) \<Longrightarrow> P (Finite_Set.fold F A Fa) \<Longrightarrow> P (F x (Finite_Set.fold F A Fa))"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
proof -

 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(simp only: UML_Set.OclIterate_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(rule fold_cong[where P = "\<lambda>s. \<forall>\<tau>. all_defined \<tau> s \<and> P s", OF downgrade EQ_comp_fun_commute.downgrade[OF G_commute], simplified image_ident])
   apply(simp only: S_all_int)
   apply(simp only: A_all_def)
   apply(rule fold_eq, simp add: int_is_valid, simp, simp)
  apply(simp, simp, simp add: A_all_def)
  apply(simp add: P0)
  apply(rule allI)
  apply(subst EQ_comp_fun_commute.all_defined_fold_rec[OF F_commute], simp add: A_all_def, simp, simp add: all_int_set_def, blast)
  apply(subst fold_insert, simp add: A_all_def, simp, simp, simp)
  apply(simp add: Prec)
  done
 qed
qed

lemma iterate_subst_set :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
by(rule iterate_subst_set_gen[OF S_all_def A_all_def F_commute G_commute fold_eq], (simp add: int_is_valid)+)

lemma iterate_subst_set' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(rule iterate_subst_set_gen[where P = "\<lambda>acc. \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>'", OF S_all_def A_all_def F_commute G_commute fold_eq], blast+)
  apply(simp add: A_include)
  apply(rule allI)+
  apply(rule cp_gen, simp, blast, blast)
 done
qed

lemma iterate_subst_set'' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (A \<tau>)\<rceil>\<rceil> \<noteq> {}"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> (\<And>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {}) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(rule iterate_subst_set_gen[where P = "\<lambda>acc. (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {})", OF S_all_def A_all_def F_commute G_commute fold_eq], blast, blast, blast)
  apply(simp add: A_notempty)
  apply(rule allI)+
  apply(rule notempty, blast, simp add: int_is_valid, blast)
 done
qed

lemma iterate_subst_set_gen0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. F (f000 x))"
     and G_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (f000 x))"
     and fold_eq : "\<And>x acc. is_int (f000 x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<tau> \<Longrightarrow> F (f000 x) acc \<tau> = G (f000 x) acc \<tau>"
     and P0 : "P A \<tau>"
     and Prec : "\<And>x Fa. \<forall>(\<tau>::'\<AA> st). all_def_set \<tau> Fa \<Longrightarrow>
           is_int (f000 x) \<Longrightarrow>
           x \<notin> Fa \<Longrightarrow>
           \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa) \<Longrightarrow>
           P (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa) \<tau> \<Longrightarrow>
           P (F (f000 x) (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa)) \<tau>"
     and f_fold_insert : "\<And>x S. x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and g_fold_insert : "\<And>x S. x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold G A (insert (f000 x) (f000 ` S)) = G (f000 x) (Finite_Set.fold G A (f000 ` S))"
     and S_lift : "all_defined \<tau> S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc)) \<tau>"
proof -
 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_all_def' : "\<And>\<tau> \<tau>'. all_defined_set' \<tau>' \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
  apply(insert S_all_def)
  apply(subst (asm) cp_all_def, simp add: all_defined_def all_defined_set'_def, blast)
 done

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(simp only: UML_Set.OclIterate_def)
  proof -
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
  apply(rule S_lift[OF S_all_def, THEN exE], simp)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: S_all_int, rule f_fold_insert, simp_all) apply(subst img_fold[OF G_commute], simp add: A_all_def, drule sym, simp add: S_all_int, rule g_fold_insert, simp_all)
  apply(rule fold_cong'[where P = "\<lambda>s \<tau>. (\<forall>\<tau>. all_defined \<tau> s) \<and> P s \<tau>", OF downgrade EQ_comp_fun_commute0_gen0.downgrade[OF G_commute], simplified image_ident])
  apply(rule all_i_set_to_def)
  apply(drule sym, simp add: S_all_int, simp add: A_all_def)
   apply(rule fold_eq, simp add: int_is_valid, blast, simp)
  apply(simp, simp, simp add: A_all_def, rule P0)
  apply(rule conjI)+
  apply(subst all_defined_fold_rec[simplified], simp add: A_all_def, simp) apply(subst def_set[THEN iffD2, THEN spec], simp) apply(simp, blast, simp)
  apply(subst fold_insert, simp add: A_all_def, simp, simp, simp)
  apply(rule Prec, simp+)
  done
 qed
qed

lemma iterate_subst_set0_gen :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<tau> \<Longrightarrow> F (\<lambda>_. x) acc \<tau> = G (\<lambda>_. x) acc \<tau>"
     and P0 : "P A \<tau>"
     and Prec : "\<And>x Fa. \<forall>(\<tau>::'\<AA> st). all_defined_set \<tau> Fa \<Longrightarrow>
           is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
           x \<notin> Fa \<Longrightarrow>
           \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<Longrightarrow>
           P (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<tau> \<Longrightarrow>
           P (F (\<lambda>_. x) (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa)) \<tau>"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc)) \<tau>"
 apply(rule iterate_subst_set_gen0[OF S_all_def A_all_def F_commute[THEN EQ_comp_fun_commute0.downgrade'] G_commute[THEN EQ_comp_fun_commute0.downgrade']])
 apply(rule fold_eq, simp, simp, simp)
 apply(rule P0, rule Prec, blast+)
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], simp add: A_all_def, blast+)
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF G_commute[THEN c000_of_c0[where f = G]], simplified], simp add: A_all_def, blast+)
done

lemma iterate_subst_set0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_:: '\<AA> st). x))) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
 apply(rule ext, rule iterate_subst_set0_gen, simp_all add: assms)
 apply(subst fold_eq, simp_all add: int_is_valid)
done

lemma iterate_subst_set'0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc \<tau>. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
 show ?thesis
  apply(rule ext, rule iterate_subst_set0_gen[where P = "\<lambda>acc _. \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>'", OF S_all_def A_all_def F_commute G_commute])
  apply(subst fold_eq, simp+, simp add: A_include)
  apply(rule allI)+
  apply(rule cp_gen', simp, blast, blast)
 done
qed

lemma iterate_subst_set''0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. x) acc \<tau> = G (\<lambda>_. x) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
 show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(rule iterate_subst_set0_gen[where P = "\<lambda>acc \<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {}", OF S_all_def A_all_def F_commute G_commute])
  apply(subst fold_eq, simp+)
  apply(rule notempty', simp+)
 done
qed

lemma iterate_subst_set___ :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and G_commute : "EQ_comp_fun_commute0' (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. \<lfloor>x\<rfloor>))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau> = G (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|F x acc)) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A|G x acc)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule F_commute)
 show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(rule iterate_subst_set_gen0[where P = "\<lambda>acc \<tau>. (\<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>') \<and> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (acc \<tau>)\<rceil>\<rceil> \<noteq> {}", OF S_all_def A_all_def F_commute[THEN EQ_comp_fun_commute0'.downgrade'] G_commute[THEN EQ_comp_fun_commute0'.downgrade']])
  apply(rule fold_eq, blast+, simp add: A_include)
  apply(rule conjI)+
  apply(rule allI)+
  apply(rule cp_gen', blast+)
  apply(rule notempty', blast+)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], simp add: A_all_def, blast+)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF G_commute[THEN c000'_of_c0'[where f = G]], simplified], simp add: A_all_def, blast+)
  apply(rule S_lift', simp add: all_defined_def)
 done
qed

subsection{* Context passing *}

lemma cp_OclIterate1_gen:
 assumes f_comm : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. f (f000 x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and f_fold_insert : "\<And>x S A. (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold f A (insert (f000 x) (f000 ` S)) = f (f000 x) (Finite_Set.fold f A (f000 ` S))"
     and S_lift : "all_defined \<tau> X \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "(X->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | f a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = (\<lambda>_. A \<tau>) | f a x)) \<tau>"
proof -
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have A_all_def' : "\<And>\<tau> \<tau>'. all_defined \<tau> (\<lambda>a. A \<tau>')" by(subst cp_all_def[symmetric], simp add: A_all_def)

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. f (f000 x)" by (rule f_comm)
 show ?thesis
 apply(subst UML_Set.cp_OclIterate[symmetric])
 apply(simp add: UML_Set.OclIterate_def cp_valid[symmetric])
 apply(case_tac "\<not>((\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>)", blast)
 apply(simp)
 apply(erule conjE)+
 apply(frule Set_inv_lemma[simplified OclValid_def])
 proof -
 assume "(\<delta> X) \<tau> = true \<tau>"
    "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
    "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> \<bottom>"
 then have X_def : "all_defined \<tau> X" by (metis (lifting, no_types) OclValid_def all_defined_def all_defined_set'_def foundation18')
 show "Finite_Set.fold f A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>) \<tau> = Finite_Set.fold f (\<lambda>_. A \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>) \<tau>"
  apply(rule S_lift[OF X_def, THEN exE], simp)
  apply(subst (1 2) img_fold[OF f_comm], simp add: A_all_def', drule sym, simp add: all_def_to_all_int[OF X_def])
  apply(rule f_fold_insert, simp_all add: A_all_def' A_all_def)+
  apply(rule fold_cong'''[where P = "\<lambda>_ _. True", OF downgrade downgrade, simplified image_ident])
  apply(rule all_i_set_to_def)
  apply(drule sym, simp add: all_def_to_all_int[OF X_def], simp add: A_all_def) apply(subst cp_all_def[symmetric], simp add: A_all_def)
  apply(blast+)
 done
 qed
qed

lemma cp_OclIterate1:
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "(X->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | f a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = (\<lambda>_. A \<tau>) | f a x)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 show ?thesis
  apply(rule cp_OclIterate1_gen[OF downgrade' A_all_def])
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF f_comm[THEN c000'_of_c0'[where f = f]], simplified], simp_all)
  apply(rule S_lift', simp add: all_defined_def)
 done
qed

subsection{* all defined (construction) *}

lemma i_cons_all_def :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (UML_Set.OclIterate S S F)"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 show ?thesis
  apply(unfold UML_Set.OclIterate_def)
  apply(simp add: A_all_def[simplified all_defined_def OclValid_def]
                  A_all_def[simplified all_defined_def all_defined_set'_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule allI, rule EQ_comp_fun_commute000.fold_def[OF F_commute[THEN c000_of_c0]], simp add: A_all_def, simp add: A_all_def')
 done
qed

lemma i_cons_all_def'' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "all_defined \<tau> (UML_Set.OclIterate S A F)"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: S_all_def)
 done

 show ?thesis
  apply(unfold UML_Set.OclIterate_def)
  apply(simp add: S_all_def[simplified all_defined_def OclValid_def]
                  S_all_def[simplified all_defined_def all_defined_set'_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule S_lift'[THEN exE, OF S_all_def[of \<tau>, simplified all_defined_def, THEN conjunct1]], simp only:)
  apply(rule allI, rule EQ_comp_fun_commute000'.fold_def[OF F_commute[THEN c000'_of_c0']], simp add: A_all_def, drule sym, simp add: A_all_def')
 done
qed

lemma i_cons_all_def''cp :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "all_defined \<tau> (\<lambda>\<tau>. UML_Set.OclIterate (\<lambda>_. S \<tau>) (\<lambda>_. A \<tau>) F \<tau>)"
 apply(subst cp_OclIterate1[symmetric, OF F_commute A_all_def])
 apply(rule i_cons_all_def''[OF F_commute S_all_def A_all_def])
done

lemma i_cons_all_def' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (UML_Set.OclIterate S S F)"
by(rule i_cons_all_def'', simp_all add: assms)

subsection{* Preservation of global jugdment *}

lemma iterate_cp_all_gen :
 assumes F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. F (f000 x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
     and f_fold_insert : "\<And>x A S. x \<notin> S \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and S_lift : "all_defined \<tau>2 S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>2)\<rceil>\<rceil> = f000 ` S'"
   shows "UML_Set.OclIterate S S F \<tau>1 = UML_Set.OclIterate S S F \<tau>2"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(unfold UML_Set.OclIterate_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set'_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  S_cp)
  apply(rule S_lift[OF A_all_def[THEN spec], THEN exE], simp)
  apply(subst (1 2) img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: A_all_def', rule f_fold_insert, simp_all add: A_all_def)
  apply(subst (1 2) image_ident[symmetric])
  apply(rule fold_cong''[where P = "\<lambda>_ _. True", OF F_commute[THEN EQ_comp_fun_commute0_gen0.downgrade] F_commute[THEN EQ_comp_fun_commute0_gen0.downgrade]])
    apply(rule all_i_set_to_def)
  apply(drule sym, simp add: A_all_def', simp add: A_all_def)
  apply(simp_all add: S_cp)
 done
qed

lemma iterate_cp_all :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
   shows "UML_Set.OclIterate S S F \<tau>1 = UML_Set.OclIterate S S F \<tau>2"
 apply(rule iterate_cp_all_gen[OF F_commute[THEN EQ_comp_fun_commute0.downgrade'] A_all_def S_cp])
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], blast+)
done

lemma iterate_cp_all' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
   shows "UML_Set.OclIterate S S F \<tau>1 = UML_Set.OclIterate S S F \<tau>2"
 apply(rule iterate_cp_all_gen[OF F_commute[THEN EQ_comp_fun_commute0'.downgrade'] A_all_def S_cp])
 apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], blast+)
 apply(rule S_lift', simp add: all_defined_def)
done

subsection{* Preservation of non-emptiness *}

lemma iterate_notempty_gen :
 assumes F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. (F:: ('\<AA>, 'a option option) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (f000 x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
     and f_fold_insert : "\<And>x A S. x \<notin> S \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and S_lift : "all_defined \<tau> S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (UML_Set.OclIterate S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(unfold UML_Set.OclIterate_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set'_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(insert S_notempty)
  apply(rule S_lift[OF A_all_def[THEN spec], THEN exE], simp)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: A_all_def', rule f_fold_insert, simp_all add: A_all_def)
  apply(subst (2) image_ident[symmetric])
   apply(rule all_int_induct)
    apply(rule all_i_set_to_def)
    apply(drule sym, simp add: A_all_def')
    apply(simp)
  apply(simp)
  apply(subst fold_insert[OF A_all_def], metis surj_pair, simp, simp)
  apply(rule notempty, rule allI, rule fold_def[simplified], simp add: A_all_def, blast+)
 done
qed

lemma iterate_notempty :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F:: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (UML_Set.OclIterate S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(rule iterate_notempty_gen[OF F_commute[THEN EQ_comp_fun_commute0.downgrade'] A_all_def S_notempty])
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], blast+)
done

lemma iterate_notempty' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (UML_Set.OclIterate S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(rule iterate_notempty_gen[OF F_commute[THEN EQ_comp_fun_commute0'.downgrade'] A_all_def S_notempty])
 apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], blast+)
 apply(rule S_lift', simp add: all_defined_def)
done

subsection{* Preservation of comp fun commute (main) *}

lemma iterate_commute' :
 assumes f_comm : "\<And>a. EQ_comp_fun_commute0' (\<lambda>x. F a (\<lambda>_. \<lfloor>x\<rfloor>))"

 assumes f_notempty : "\<And>S x y \<tau>. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
            is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
            (\<forall>(\<tau>::'\<AA> st). all_defined \<tau> S) \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            UML_Set.OclIterate (UML_Set.OclIterate S S (F x)) (UML_Set.OclIterate S S (F x)) (F y) \<tau> =
            UML_Set.OclIterate (UML_Set.OclIterate S S (F y)) (UML_Set.OclIterate S S (F y)) (F x) \<tau>"

 shows "EQ_comp_fun_commute0' (\<lambda>x S. S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;S=S | F x j S))"
 proof - interpret EQ_comp_fun_commute0' "\<lambda>x. F a (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 apply_end(simp only: EQ_comp_fun_commute0'_def)
 apply_end(rule conjI)+ apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(subst cp_OclIterate1[OF f_comm], blast, simp)
 apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(subst iterate_cp_all', simp add: f_comm, simp, simp, simp)

 apply_end(rule conjI)+ apply_end(rule allI)+ apply_end(rule impI)+

 show "\<And>x S \<tau>.
        \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow>
        is_int (\<lambda>_. \<lfloor>x\<rfloor>) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (UML_Set.OclIterate S S (F x) \<tau>)\<rceil>\<rceil> \<noteq> {}"
 by(rule iterate_notempty'[OF f_comm], simp_all)

 apply_end(rule conjI)+ apply_end(rule allI)+
 fix x y \<tau>
 show "(\<forall>\<tau>. all_defined \<tau> (UML_Set.OclIterate y y (F x))) = (is_int (\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  apply(rule iffI, rule conjI) apply(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)
  apply(rule i_invert_all_defined'[where F = "F x"], simp)
  apply(rule allI, rule i_cons_all_def'[where F = "F x", OF f_comm], blast)
 done

 apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(rule ext, rename_tac \<tau>)
 fix S and x and y and \<tau>
 show " is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
             is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
             (\<forall>(\<tau>::'\<AA> st). all_defined \<tau> S) \<Longrightarrow>
             UML_Set.OclIterate (UML_Set.OclIterate S S (F x)) (UML_Set.OclIterate S S (F x)) (F y) \<tau> =
             UML_Set.OclIterate (UML_Set.OclIterate S S (F y)) (UML_Set.OclIterate S S (F y)) (F x) \<tau> "
  apply(case_tac "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply(metis (hide_lams, no_types) abs_rep_simp' all_defined_def)
  apply(simp add: mtSet_def)

  apply(subst (1 2) cp_OclIterate1[OF f_comm]) apply(rule i_cons_all_def'[OF f_comm], blast)+
  apply(subst (1 2 3 4 5 6) cp_OclIterate1[OF f_comm])
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm], blast) apply(blast)
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm], blast)
  apply(simp)
  apply(subst (1 2 3 4 5 6) cp_OclIterate1[OF f_comm, symmetric])
   apply(subst (1 2) cp_mtSet[symmetric])
    apply(rule i_cons_all_def'[OF f_comm]) apply(simp add: mtSet_all_def)+
   apply(subst (1 2) cp_mtSet[symmetric])
    apply(rule i_cons_all_def'[OF f_comm]) apply(simp add: mtSet_all_def)+

  apply(subst (1 2) cp_OclIterate1[OF f_comm])
   apply(rule i_cons_all_def'[OF f_comm], metis surj_pair)
   apply(rule i_cons_all_def'[OF f_comm], metis surj_pair)
  apply(subst (1 2 3 4 5 6) cp_OclIterate1[OF f_comm])
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm]) apply(metis surj_pair)+
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm]) apply(metis surj_pair)+
  apply(subst (1 2 3 4 5 6) cp_OclIterate1[OF f_comm, symmetric])
   apply(rule i_cons_all_def''cp[OF f_comm]) apply(metis surj_pair) apply(metis surj_pair) apply(metis surj_pair)
   apply(rule i_cons_all_def''cp[OF f_comm]) apply(metis surj_pair) apply(metis surj_pair)

  apply(rule f_notempty, simp_all)

 done
qed

section{* Properties: (with comp fun commute) OclIterate and OclIncluding *}
subsection{* Identity *}

lemma i_including_id'_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
   shows "(Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = S \<tau>"
proof -
 have invert_set_0 : "\<And>x F. \<lfloor>\<lfloor>insert x F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lfloor>\<lfloor>F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(auto simp: bot_option_def null_option_def)

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done
 show "Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> = S \<tau>"
  apply(subst finite_induct[where P = "\<lambda>set. all_defined_set \<tau> set \<and> \<lfloor>\<lfloor>set\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<longrightarrow>
                                             (\<forall>(s :: ('\<AA>, _) Set). (\<forall>\<tau>. all_defined \<tau> s) \<longrightarrow>
                                                  (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>j r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(j))) s ((\<lambda>a \<tau>. a) ` set)))) \<and>
                                             (\<forall>s. (\<forall>\<tau>. all_defined \<tau> s) \<and> (set \<subseteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (s \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                                                  (Finite_Set.fold (\<lambda>j r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(j))) s ((\<lambda>a \<tau>. a) ` set)) \<tau> = s \<tau>)"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])
  apply(simp)
  defer
  apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>], frule Set_inv_lemma)
  apply(simp add: foundation18 all_defined_set_def invalid_def S_all_def[simplified all_defined_def all_defined_set'_def])
  apply (metis assms order_refl)
  apply(simp)

  (* *)
  apply(rule impI) apply(erule conjE)+
  apply(drule invert_set_0, simp del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
  apply(frule invert_all_def_set, simp del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
  apply(erule conjE)+

  (* *)
  apply(rule conjI)
  apply(rule allI, rename_tac SSS, rule impI, rule allI, rule allI)
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF _ including_commute], simp)
  apply(simp)
  apply(simp add: all_int_set_def all_defined_set_def is_int_def) apply (metis (mono_tags) foundation18')
  apply(simp)
  (* *)
  apply(rule allI, rename_tac SS, rule impI)
  apply(drule all_def_to_all_int_)+
  apply(subst EQ_comp_fun_commute.fold_insert[where f = "(\<lambda>j r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))", OF including_commute])
  apply(case_tac \<tau>', simp only:)
  apply(simp)+
  apply(rule invert_int, simp)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(simp)
  apply(subst including_id')
  apply(metis prod.exhaust)
  apply(auto)
 done
qed

lemma iterate_including_id_generic :
   assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     shows "(S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j))) = S"
  apply(simp add: UML_Set.OclIterate_def OclValid_def del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec, rule ext)
  apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
   prefer 2
   proof -
   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
   apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set'_def]
                   foundation20[simplified OclValid_def])
   done
  apply_end(subst i_including_id'_generic[OF including_commute], simp_all add: S_all_def)
qed

lemma i_including_id00_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ((S :: ('\<AA>, 'a option option) Set) \<tau>)\<rceil>\<rceil>)"
   shows "\<And>\<tau>. \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a) ; set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x) in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set') = S')"
proof -
 have S_incl : "\<forall>(x :: ('\<AA>, 'a option option) Set). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
  apply(rule allI) apply(rule impI)+
  apply(rule ext, rename_tac \<tau>)
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(simp add: mtSet_def)
 by (metis (hide_lams, no_types) abs_rep_simp' all_defined_def)

 have invert_set_0 : "\<And>x F. \<lfloor>\<lfloor>insert x F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lfloor>\<lfloor>F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(auto simp: bot_option_def null_option_def)

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have rec : "\<And>x (F :: ('\<AA>,'a option option) val set). all_int_set F \<Longrightarrow>
            is_int x \<Longrightarrow>
            x \<notin> F \<Longrightarrow>
            \<forall>x. (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow>
                (let img = (`) (\<lambda>a \<tau>. a); set' = F; f = \<lambda>x. x
                 in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set' = x) \<Longrightarrow>
            \<forall>xa. (\<forall>\<tau>. all_defined \<tau> xa) \<longrightarrow>
                 (let img = (`) (\<lambda>a \<tau>. a); set' = insert x F; f = \<lambda>x. x
                  in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (xa \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set' = xa)"
  apply(simp only: Let_def image_ident)

  proof - fix \<tau> fix x fix F :: "('\<AA>,'a option option) val set"
   show "all_int_set F \<Longrightarrow>
            is_int x \<Longrightarrow>
            x \<notin> F \<Longrightarrow>
            \<forall>x. (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. F = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) Set{} F = x \<Longrightarrow>
            \<forall>xa. (\<forall>\<tau>. all_defined \<tau> xa) \<longrightarrow> (\<forall>\<tau>. insert x F = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (xa \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) Set{} (insert x F) = xa"
  apply(rule allI, rename_tac S) apply(rule impI)+
  apply(subst sym[of "insert x F"], blast)
  apply(drule_tac x = "S->excluding\<^sub>S\<^sub>e\<^sub>t(x)" in allE) prefer 2 apply assumption
  apply(subgoal_tac "\<And>\<tau>. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) - {x}", simp only:)
  apply(subgoal_tac "(\<forall>\<tau>. all_defined \<tau> S->excluding\<^sub>S\<^sub>e\<^sub>t(x))")
   prefer 2
   apply(rule allI)
   apply(rule cons_all_def_e, metis)
   apply(rule int_is_valid, simp)
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute]) prefer 5
  apply(drule arg_cong[where f = "\<lambda>S. (S->including\<^sub>S\<^sub>e\<^sub>t(x))"], simp)
  apply(rule Ocl_insert_Diff)
   apply(metis surj_pair)
   apply(subst sym[of "insert x F"], metis surj_pair)
   apply(simp)+
   apply(subst mtSet_all_def)
   apply(simp)+
  apply(subst excluding_unfold)
  apply(metis surj_pair)
  apply(rule int_is_valid, simp)
  apply(subst image_set_diff, simp add: inject)
  apply(simp)
  apply(drule destruct_int)
    apply(frule_tac P = "\<lambda>j. x = (\<lambda>_. j)" in ex1E) prefer 2 apply assumption
  apply(blast)
  done
 qed

 fix \<tau>
 show "\<forall>S'.  (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a); set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x)  in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set') = S')"
  apply(rule allI)
  proof - fix S' :: "('\<AA>, _) Set" show "(\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = (`) (\<lambda>a \<tau>. a); set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
           in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set' = S')"
   apply(simp add: Let_def, rule impI)
   apply(subgoal_tac "(let img = (`) (\<lambda>a \<tau>. a); set' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
    in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set' = S')") prefer 2

   apply(subst EQ_comp_fun_commute.all_int_induct[where P = "\<lambda>set.
   \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a)
     ; set' = set ; f = (\<lambda>x. x) in
                 (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                 (Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(f j)) Set{} set') = S')"
                                 and F = "(\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", OF including_commute, THEN spec, of S'])
   apply(simp add: S_all_int)
   apply(simp add: S_incl)
   apply(rule rec)
   apply(simp) apply(simp) apply(simp) apply(simp) apply(simp)
   apply(blast)

   apply(simp add: Let_def)

  done
 qed
qed

lemma iterate_including_id00_generic :
   assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
       and S_incl : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
     shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=Set{} | r2->including\<^sub>S\<^sub>e\<^sub>t(j))) = S"
 apply(simp add: UML_Set.OclIterate_def OclValid_def del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec, rule ext)
 apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 prefer 2
  proof -
   have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
   by(rule all_def_to_all_int, simp add: assms)

   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
     apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set'_def]
                     foundation20[simplified OclValid_def])
  done
 fix \<tau> show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)) Set{} ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau> = S \<tau>"
  apply(subst i_including_id00_generic[OF including_commute, simplified Let_def image_ident, where S = S and \<tau> = \<tau>])
   prefer 4
   apply(rule refl)
   apply(simp add: S_all_int S_all_def)+
 by (metis S_incl)
qed

subsection{* all defined (construction) *}

lemma preserved_defined_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: ('\<AA>, 'a option option) Set)"
   shows "let S' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> in
          \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A S')"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 show ?thesis
  apply(subst Let_def)
  apply(rule finite_induct[where P = "\<lambda>set.
                                                let set' = (\<lambda>a \<tau>. a) ` set in
                                                all_int_set set' \<longrightarrow>
                                                (\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A set'))"
                               and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp])
  apply(simp add: S_all_def[where \<tau> = \<tau>, simplified all_defined_def all_defined_set'_def])
  apply(simp add: A_all_def)
  apply(rule impI, simp only: image_insert, rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp])
  apply(simp add: A_all_def)
  apply(simp add: including_commute)
  apply(simp)
  apply(simp)
  apply(drule invert_all_int_set, simp)

  apply(rule all_def_to_all_int[OF S_all_def])
 done
qed

subsection{* Preservation of comp fun commute (main) *}

lemma iterate_including_commute :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). x} Set{\<lambda>(_:: '\<AA> st). x} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) =
                UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). y} Set{\<lambda>(_:: '\<AA> st). y} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
            \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (UML_Set.OclIterate ((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) ((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) \<tau> =
                (UML_Set.OclIterate ((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) ((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x) \<tau> "
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | F j r2)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)


 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(subst (1 2) UML_Set.OclIncluding.cp0, subst cp_OclIterate1[OF f_comm[THEN c0'_of_c0]], blast, simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_cp_all, simp, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast)
  apply(rule iterate_cp_all, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(rule including_notempty, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: int_is_valid)
  apply(rule iterate_notempty, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+
  apply(rule iffI)
  apply(drule invert_all_defined', erule conjE, rule conjI, simp)
  apply(rule i_invert_all_defined'[where F = F], simp)
  apply(rule allI, rule cons_all_def, rule i_cons_all_def[OF f_comm], blast, simp add: int_is_valid)
  apply(rule allI)+ apply(rule impI)+

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply(metis (hide_lams, no_types) abs_rep_simp' all_defined_def)
  apply(simp add: mtSet_def)

  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) cp_OclIterate1[OF f_comm[THEN c0'_of_c0]])
   apply(rule cons_all_def') apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], blast)+ apply(simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], blast)+ apply(simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 4 5) cp_OclIterate1[OF f_comm[THEN c0'_of_c0]], blast)
  apply(simp)
  apply(subst (1 2 4 5) cp_OclIterate1[OF f_comm[THEN c0'_of_c0], symmetric], simp add: mtSet_all_def)
  apply(simp)
  apply(subst (1 2 4 5) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst (1 2 3 4) cp_singleton)
  apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst f_empty, simp_all)

  apply(rule com, simp_all)
 done
qed

lemma iterate_including_commute_var_generic :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. (F :: ('\<AA>, 'a option option) val
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
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(subst (1 2) UML_Set.OclIncluding.cp0, subst (1 2 3 4) UML_Set.OclIncluding.cp0, subst cp_OclIterate1[OF f_comm[THEN c0'_of_c0]], blast, simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_cp_all, simp, rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule including_cp_all, simp add: a_int, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule iterate_cp_all, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(rule including_notempty, rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule iterate_notempty, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+
  apply(rule iffI)
  apply(drule invert_all_defined', erule conjE, rule conjI, simp)
  apply(rule destruct_int[OF a_int, THEN ex1_implies_ex, THEN exE], rename_tac a', simp only:)
  apply(drule invert_all_defined', erule conjE)
  apply(rule i_invert_all_defined'[where F = F], simp)
  apply(rule allI, rule cons_all_def, rule cons_all_def, rule i_cons_all_def[OF f_comm], blast) apply(simp add: int_is_valid a_int)+
  apply((rule allI)+, (rule impI)+)+

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply (metis (hide_lams, no_types) abs_rep_simp' all_defined_def prod.exhaust)
  apply(simp add: mtSet_def)


  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) cp_OclIterate1[OF f_comm[THEN c0'_of_c0]])
   apply(rule cons_all_def')+ apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], metis surj_pair) apply(simp add: a_int int_is_valid)+
   apply(rule cons_all_def')+ apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], metis surj_pair) apply(simp add: a_int int_is_valid)+
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8 9 10 11 12) UML_Set.OclIncluding.cp0)

  apply(subst (1 2 4 5) cp_OclIterate1[OF f_comm[THEN c0'_of_c0]], metis surj_pair)
  apply(simp)
  apply(subst (1 2 4 5) cp_OclIterate1[OF f_comm[THEN c0'_of_c0], symmetric], simp add: mtSet_all_def)
  apply(simp)
  apply(subst (1 2 3 4 7 8 9 10) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst (1 2 3 4) cp_doubleton, simp add: int_is_const[OF a_int])
  apply(subst (1 2 3 4) UML_Set.OclIncluding.cp0[symmetric])

  apply(subst (3 6) OclIncluding_commute)
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int)+

  apply(subst f_empty, simp_all)

  apply(subst (3 6) OclIncluding_commute)
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int)+

  apply(rule com, simp_all)
 done
qed

subsection{* Execution (OclIterate, OclIncluding to OclExcluding) *}

lemma EQ_OclIterate_including:
 assumes S_all_int: "\<And>(\<tau>::'\<AA> st). all_int_set ((\<lambda> a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 assumes S_all_def:    "\<And>\<tau>. all_defined \<tau> S"
 and     A_all_def:    "\<And>\<tau>. all_defined \<tau> A"
 and     F_commute:   "EQ_comp_fun_commute F"
 and     a_int : "is_int a"
 shows   "((S->including\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x =     A | F a x)) =
          ((S->excluding\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = F a A | F a x))"
proof -

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have F_cp : "\<And> x y \<tau>. F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix x y \<tau> show "F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
   by(rule F_cp)
 qed

 have F_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> (F a A)"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix \<tau> show "\<tau> \<Turnstile> \<upsilon> (F a A)"
  apply(insert
    all_def
    int_is_valid[OF a_int]
    A_all_def, simp add: all_defined1 foundation20)
  done
 qed

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 have insert_in_Set_0 : "\<And>\<tau>. ?this \<tau>"
  apply(rule insert_in_Set_0)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  apply(rule insert_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  apply(rule insert_in_Set_0, simp_all add: null_option_def bot_option_def)
 done
 have insert_defined : "\<And>\<tau>. ?this \<tau>"
  apply(rule insert_defined)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have remove_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have remove_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
  proof - fix \<tau> show "?thesis \<tau>"
   apply(insert S_all_int[of \<tau>], simp add: all_int_set_def, rule remove_finite)
   apply(erule conjE, drule finite_imageD)
   apply (metis inj_onI, simp)
  done
 qed

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: foundation18 invalid_def)
 done
 have remove_in_Set_0 : "\<And>\<tau>. ?this \<tau>"
  apply(rule remove_in_Set_0)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  apply(rule remove_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  apply(rule remove_in_Set_0, simp_all add: null_option_def bot_option_def)
 done
 have remove_defined : "\<And>\<tau>. ?this \<tau>"
  apply(rule remove_defined)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  proof - fix \<tau> show "UML_Set.OclIterate S->including\<^sub>S\<^sub>e\<^sub>t(a) A F \<tau> = UML_Set.OclIterate S->excluding\<^sub>S\<^sub>e\<^sub>t(a) (F a A) F \<tau>"
   apply(simp only: UML_Set.cp_OclIterate[of "S->including\<^sub>S\<^sub>e\<^sub>t(a)"] UML_Set.cp_OclIterate[of "S->excluding\<^sub>S\<^sub>e\<^sub>t(a)"])
   apply(subst UML_Set.OclIncluding_def, subst UML_Set.OclExcluding_def)

   apply(simp add: S_all_def[simplified all_defined_def OclValid_def] int_is_valid[OF a_int, simplified OclValid_def])

   apply(simp add: UML_Set.OclIterate_def)
   apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF insert_in_Set_0] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF remove_in_Set_0]
                   foundation20[OF all_defined1[OF A_all_def], simplified OclValid_def]
                   S_all_def[simplified all_defined_def all_defined_set_def]
                   insert_defined
                   remove_defined
                   F_val[of \<tau>, simplified OclValid_def])

   apply(subst EQ_comp_fun_commute.fold_fun_comm[where f = F and z = A and x = a and A = "((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))", symmetric, OF F_commute A_all_def _ int_is_valid[OF a_int]])
   apply(simp add: remove_all_int)

   apply(subst image_set_diff[OF inject], simp)
   apply(subgoal_tac "Finite_Set.fold F A (insert (\<lambda>\<tau>'. a \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> =
       F (\<lambda>\<tau>'. a \<tau>) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {\<lambda>\<tau>'. a \<tau>})) \<tau>")
   apply(subst F_cp)
   apply(simp)

   apply(subst EQ_comp_fun_commute.fold_insert_remove[OF F_commute A_all_def S_all_int])
   apply (metis (mono_tags) a_int foundation18' is_int_def)
   apply(simp)
  done
 qed
qed

lemma (*EQ_OclIterate_including':*)
 assumes S_all_int: "\<And>(\<tau>::'\<AA> st). all_int_set ((\<lambda> a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 assumes S_all_def:    "\<And>\<tau>. all_defined \<tau> S"
 and     A_all_def:    "\<And>\<tau>. all_defined \<tau> A"
 and     F_commute:   "EQ_comp_fun_commute F"
 and     a_int : "is_int a"
 shows   "((S->including\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x =     A | F a x)) =
          F a ((S->excluding\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | F a x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have F_cp_set : "\<And> x S \<tau>. F x S \<tau> = F x (\<lambda> _. S \<tau>) \<tau>"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix x S \<tau> show "F x S \<tau> = F x (\<lambda> _. S \<tau>) \<tau>"
   by(rule F_cp_set)
 qed

 have F_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> (F a A)"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix \<tau> show "\<tau> \<Turnstile> \<upsilon> (F a A)"
  apply(insert
    all_def
    int_is_valid[OF a_int]
    A_all_def, simp add: all_defined1 foundation20)
  done
 qed

 have remove_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have remove_finite': "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(a) \<tau>)\<rceil>\<rceil>"
  apply(subst excluding_unfold)
 by(simp add: S_all_def int_is_valid[OF a_int] S_all_def[simplified all_defined_def all_defined_set'_def])+

 have remove_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
  proof - fix \<tau> show "?thesis \<tau>"
   apply(insert S_all_int[of \<tau>], simp add: all_int_set_def, rule remove_finite)
   apply(erule conjE, drule finite_imageD)
   apply (metis inj_onI, simp)
  done
 qed

 have remove_all_int' : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(a) \<tau>)\<rceil>\<rceil>))"
  apply(subst excluding_unfold)
 by(simp add: S_all_def int_is_valid[OF a_int] remove_all_int)+

 show ?thesis
  apply(simp add: EQ_OclIterate_including[OF S_all_int S_all_def A_all_def F_commute a_int])
  apply(rule ext, rename_tac \<tau>)
  proof - fix \<tau> show "UML_Set.OclIterate S->excluding\<^sub>S\<^sub>e\<^sub>t(a) (F a A) F \<tau> = F a (UML_Set.OclIterate S->excluding\<^sub>S\<^sub>e\<^sub>t(a) A F) \<tau>"
   apply(simp add: UML_Set.OclIterate_def)
   apply(simp add: foundation20[OF all_defined1[OF A_all_def], simplified OclValid_def]
                   S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                   int_is_valid[OF a_int, simplified OclValid_def]
                   F_val[of \<tau>, simplified OclValid_def]
                   foundation10[simplified OclValid_def]
                   remove_finite')

   apply(subst EQ_comp_fun_commute.fold_fun_comm[where f = F and z = A and x = a and A = "((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(a) \<tau>)\<rceil>\<rceil>))", symmetric, OF F_commute A_all_def _ int_is_valid[OF a_int]])
   apply(simp add: remove_all_int')
   apply(subst (1 2) F_cp_set, simp)
  done
 qed
qed

subsection{* Execution OclIncluding out of OclIterate (theorem) *}

lemma including_out1_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes including_commute2 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
proof -

 have i_valid : "\<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i"
 by (metis i_int int_is_valid)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)


 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done


 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)


 have invert_all_defined_fold : "\<And> F x a b. let F' = (\<lambda>a \<tau>. a) ` F in x \<notin> F \<longrightarrow> all_int_set (insert (\<lambda>\<tau>. x) F') \<longrightarrow> all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A (insert (\<lambda>\<tau>. x) F')) \<longrightarrow>
               all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A F')"
 proof - fix F x a b show "?thesis F x a b"
  apply(simp add: Let_def) apply(rule impI)+
  apply(insert arg_cong[where f = "\<lambda>x. all_defined (a, b) x", OF EQ_comp_fun_commute.fold_insert[OF including_commute, where x= "(\<lambda>\<tau>. x)" and A = "(\<lambda>a \<tau>. a) ` F" and z = A]]
               allI[where P = "\<lambda>x. all_defined x A", OF A_all_def])
  apply(simp)
  apply(subgoal_tac "all_int_set ((\<lambda>a \<tau>. a) ` F)")
  prefer 2
  apply(simp add: all_int_set_def, auto)
  apply(drule invert_int, simp)
  apply(subgoal_tac "(\<lambda>(\<tau>:: '\<AA> st). x) \<notin> (\<lambda>a (\<tau>:: '\<AA> st). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i' x F. i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x))->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(j))) A ((\<lambda>a \<tau>. a) ` F))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x))->including\<^sub>S\<^sub>e\<^sub>t(i))"
 proof - fix i' x F show "i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow> ?thesis i' x F"
 by(simp only: OclIncluding_idem)
 qed

 have i_out1 : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
        Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) =
        (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))->including\<^sub>S\<^sub>e\<^sub>t(i)"
 proof - fix \<tau> show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
         Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) =
         (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))->including\<^sub>S\<^sub>e\<^sub>t(i)"
  apply(subst finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. a) ` set
                                               ; fold_set = Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A set' in
                                               (\<forall>\<tau>. all_defined \<tau> fold_set) \<and>
                                               set' \<noteq> {} \<longrightarrow>
                                               all_int_set set' \<longrightarrow>
                                               (Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) A set') =
                                               (fold_set->including\<^sub>S\<^sub>e\<^sub>t(i))"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simplified Let_def])
  apply(simp add: S_finite)
  apply(simp)
  defer

  apply(subst preserved_defined_generic[OF including_commute, where \<tau> = \<tau>, simplified Let_def])
  apply(simp add: S_all_def)
  apply(simp add: A_all_def)
  apply(simp)

  apply(rule all_def_to_all_int, simp add: S_all_def)
  apply(simp add: UML_Set.OclIncluding.cp0[of _ i])

  (* *)
  apply(rule impI)+ apply(erule conjE)+
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute])
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute2])
  apply(simp add: i_int)
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subgoal_tac "(\<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` F)))")
  prefer 2
  apply(rule allI) apply(erule_tac x = a in allE)
  apply(rule allI) apply(erule_tac x = b in allE)
  apply(simp add: invert_all_defined_fold[simplified Let_def, THEN mp, THEN mp, THEN mp])

  apply(simp)

  (* *)
  apply(case_tac "F = {}", simp)
  apply(simp add: all_int_set_def)
  done
 qed

 show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp add: UML_Set.OclIterate_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def])
  apply(drule i_out1)
  apply(simp add: UML_Set.OclIncluding.cp0[of _ i])
 done
qed

lemma including_out2_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
 assumes including_commute2 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 assumes including_commute3 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(x)))"
 assumes including_commute4 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes including_commute5 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i))"
 assumes including_out1 : "\<And>S A i \<tau>. (\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int i \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
 assumes preserved_defined : "\<And>(S :: ('\<AA>, 'a option option) Set) (A :: ('\<AA>, 'a option option) Set) \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
(\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> let S' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> in \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A S')"

 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     and x0_int : "is_int x0"
     shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
proof -
 have x0_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x0" apply(insert x0_int[simplified is_int_def]) by (metis foundation18')
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" apply(insert i_int[simplified is_int_def]) by (metis foundation18')

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have init_out1 : "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
  apply(rule iterate_subst_set[OF S_all_def A_all_def including_commute4 including_commute5])
  apply(simp add: x0_int i_int)+
 done

 have init_out2 : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
  apply(rule including_subst_set'') prefer 4
  apply(simp add: including_out1[OF S_all_def A_all_def x0_int, symmetric])
  apply(subst iterate_subst_set[OF S_all_def A_all_def including_commute3 including_commute2])
  apply(simp add: x0_int)+ apply(rule x0_int)
  apply(simp)
  (* *)
  apply(rule all_defined1)
  apply(rule i_cons_all_def'') apply(rule including_commute2[THEN c0_of_c, THEN c0'_of_c0], simp add: x0_int, simp add: S_all_def, simp add: A_all_def)
  apply(rule all_defined1)
  apply(rule cons_all_def)
  apply(rule i_cons_all_def'') apply(rule including_commute[THEN c0_of_c, THEN c0'_of_c0], simp add: x0_int, simp add: S_all_def, simp add: A_all_def, simp add: int_is_valid[OF x0_int])
  apply(simp add: int_is_valid[OF i_int])
 done

 have i_valid : "\<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i"
 by (metis i_int int_is_valid)


 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)


 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done


 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)


 have invert_all_defined_fold : "\<And> F x a b. let F' = (\<lambda>a \<tau>. a) ` F in x \<notin> F \<longrightarrow> all_int_set (insert (\<lambda>\<tau>. x) F') \<longrightarrow> all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A (insert (\<lambda>\<tau>. x) F')) \<longrightarrow>
               all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A F')"
 proof - fix F x a b show "?thesis F x a b"
  apply(simp add: Let_def) apply(rule impI)+
  apply(insert arg_cong[where f = "\<lambda>x. all_defined (a, b) x", OF EQ_comp_fun_commute.fold_insert[OF including_commute, where x= "(\<lambda>\<tau>. x)" and A = "(\<lambda>a \<tau>. a) ` F" and z = A]]
               allI[where P = "\<lambda>x. all_defined x A", OF A_all_def])
  apply(simp)
  apply(subgoal_tac "all_int_set ((\<lambda>a \<tau>. a) ` F)")
  prefer 2
  apply(simp add: all_int_set_def, auto)
  apply(drule invert_int, simp)
  apply(subgoal_tac "(\<lambda>(\<tau>:: '\<AA> st). x) \<notin> (\<lambda>a (\<tau>:: '\<AA> st). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i i' x F. is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x))->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including\<^sub>S\<^sub>e\<^sub>t(j))) A ((\<lambda>a \<tau>. a) ` F))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x))->including\<^sub>S\<^sub>e\<^sub>t(i))"
 by simp

 have destruct3 : "\<And>A B C \<tau>. (\<tau> \<Turnstile> A) \<and> (\<tau> \<Turnstile> B) \<and> (\<tau> \<Turnstile> C) \<Longrightarrow> (\<tau> \<Turnstile> (A and B and C))"
 by (metis foundation10 foundation6)

 have i_out1 : "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
        Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) =
        (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)"
 proof - fix \<tau> show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
         Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) =
         (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)"
  apply(subst finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. a) ` set
                                               ; fold_set = Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))) A set' in
                                               (\<forall>\<tau>. all_defined \<tau> fold_set) \<and>
                                               set' \<noteq> {} \<longrightarrow>
                                               all_int_set set' \<longrightarrow>
                                               (Finite_Set.fold (\<lambda>x acc. (acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i)) A set') =
                                               (fold_set->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(i))"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simplified Let_def])
  apply(simp add: S_finite)
  apply(simp)
  defer

  apply(subst preserved_defined[where \<tau> = \<tau>, simplified Let_def])
  apply(simp add: S_all_def)
  apply(simp add: A_all_def)
  apply(simp)

  apply(rule all_def_to_all_int, simp add: S_all_def)
  apply(simp add: UML_Set.OclIncluding.cp0[of _ i])

  (* *)
  apply(rule impI)+ apply(erule conjE)+
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute])
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute5])
  apply(simp add: x0_int)
  apply(simp add: i_int)
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subgoal_tac "(\<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)) A ((\<lambda>a \<tau>. a) ` F)))")
  prefer 2
  apply(rule allI) apply(erule_tac x = a in allE)
  apply(rule allI) apply(erule_tac x = b in allE)
  apply(simp add: invert_all_defined_fold[simplified Let_def, THEN mp, THEN mp, THEN mp])

  apply(simp)

  (* *)
  apply(case_tac "F = {}", simp)
  apply(simp add: all_int_set_def)
  done
 qed

 show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp only: init_out1, subst init_out2, simp del: OclIncluding_commute)
  apply(simp add: UML_Set.OclIterate_def del: OclIncluding_commute)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def]
             del: OclIncluding_commute)
  apply(simp add: i_out1 del: OclIncluding_commute)
  apply(simp add: UML_Set.OclIncluding.cp0[of _ i] UML_Set.OclIncluding.cp0[of _ x0])
 done
qed

lemma including_out0_generic :
   assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
       and S_include : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
       and S_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
       and a_int : "is_int a"
     shows "(S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=Set{a} | acc->including\<^sub>S\<^sub>e\<^sub>t(x))) = (S->including\<^sub>S\<^sub>e\<^sub>t(a))"

 apply(rule ex1E[OF destruct_int[OF a_int]], rename_tac a', simp)
 apply(case_tac "\<forall>\<tau>. a' \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>")
proof -
 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have a_all_def : "\<And>\<tau>. all_defined \<tau> Set{a}"
 by(rule cons_all_def, rule mtSet_all_def, simp add: int_is_valid[OF a_int])

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have Sa_include : "\<And>a' \<tau> \<tau>'. (\<lambda>_. a') = a \<Longrightarrow> S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>'"
 apply(simp add: UML_Set.OclIncluding.cp0[of _ a])
 apply(drule sym[of _ a], simp add: UML_Set.OclIncluding.cp0[symmetric])
  proof - fix a' \<tau> \<tau>' show "a = (\<lambda>_. a') \<Longrightarrow> \<lambda>_. S \<tau>->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. a') \<tau> = \<lambda>_. S \<tau>'->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. a') \<tau>'"
   apply(simp add: UML_Set.OclIncluding_def)
   apply(drule sym[of a])
   apply(simp add: cp_defined[symmetric])
   apply(simp add: all_defined1[OF S_all_def, simplified OclValid_def] int_is_valid[OF a_int, simplified OclValid_def])
   apply(subst S_include[of \<tau> \<tau>'], simp)
  done
 qed

 have gen_all : "\<And>a. \<exists> \<tau>. a \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<forall> \<tau>. a \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
  apply(rule allI)
  apply(drule exE) prefer 2 apply assumption
 by(subst S_include, simp)

 fix a' show "a = (\<lambda>_. a') \<Longrightarrow> \<forall>\<tau>. a' \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=Set{\<lambda>_. a'} | acc->including\<^sub>S\<^sub>e\<^sub>t(x))) = S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. a')"
  apply(subst including_id[OF S_all_def, symmetric], simp)
  apply(drule sym[of a], simp)
  apply(subst EQ_OclIterate_including[where a = a and A = "Set{a}" and F = "\<lambda>a A. (A->including\<^sub>S\<^sub>e\<^sub>t(a))", simplified flatten_int, OF S_all_int S_all_def a_all_def including_commute a_int])
  apply(subst EQ_OclIterate_including[where a = a and A = "Set{}" and F = "\<lambda>a A. (A->including\<^sub>S\<^sub>e\<^sub>t(a))", symmetric, OF S_all_int S_all_def mtSet_all_def including_commute a_int])
  apply(rule iterate_including_id00_generic[OF including_commute])
  apply(rule cons_all_def, simp_all add: S_all_def int_is_valid[OF a_int])
  apply(simp add: Sa_include)
 done
 apply_end simp_all

 fix a'
 show "a = (\<lambda>_. a') \<Longrightarrow>
         \<forall>y. (\<lambda>_. a') = (\<lambda>_. y) \<longrightarrow> y = a' \<Longrightarrow> \<exists>a b. a' \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S (a, b))\<rceil>\<rceil> \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=Set{\<lambda>_. a'} | acc->including\<^sub>S\<^sub>e\<^sub>t(x))) = S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. a')"
  apply(drule gen_all[simplified])
  apply(subst excluding_id[OF S_all_def, symmetric])
  prefer 2 apply (simp)
  apply(drule sym[of a], simp add: a_int)
  apply(drule sym[of a], simp)
  apply(subst EQ_OclIterate_including[where a = a and A = "Set{}" and F = "\<lambda>a A. (A->including\<^sub>S\<^sub>e\<^sub>t(a))", symmetric, OF S_all_int S_all_def mtSet_all_def including_commute a_int])
  apply(rule iterate_including_id00_generic[OF including_commute])
  apply(rule cons_all_def, simp_all add: S_all_def int_is_valid[OF a_int])
  apply(simp add: Sa_include)
 done
qed

subsection{* Execution OclIncluding out of OclIterate (corollary) *}

lemma iterate_including_id_out_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
 assumes including_commute2 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 assumes including_commute3 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(x)))"
 assumes including_out1 : "\<And>S A i \<tau>. (\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int i \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"

 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
 apply(subst iterate_subst_set0[where G = "\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(a)"])
  apply(simp add: S_def)
  apply(rule including_commute3[THEN c0_of_c], simp add: a_int)
  apply(rule including_commute2[THEN c0_of_c], simp add: a_int)
  apply(simp)
  apply(subst including_out1) apply(simp add: S_def a_int)+
  apply(subst iterate_including_id_generic[OF including_commute], simp add: S_def, simp)
done
qed

lemma iterate_including_id_out'_generic :
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). (r2->including\<^sub>S\<^sub>e\<^sub>t(j)))"
 assumes including_out1 : "\<And>(S:: ('\<AA>, 'a option option) Set) A i \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
          (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
          is_int i \<Longrightarrow>
          \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i) \<tau>"
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(a))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
  apply(subst including_out1) apply(simp add: S_def a_int)+
  apply(subst iterate_including_id_generic[OF including_commute], simp add: S_def, simp)
done

lemma iterate_including_id_out''''_generic :
 assumes including_out2 : "\<And>S A i x0 \<tau>.
                           (\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                           (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
                           is_int i \<Longrightarrow>
                           is_int x0 \<Longrightarrow>
                           \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
 assumes including_commute3 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(x)))"
 assumes iterate_including_id_out : "\<And>S a \<tau>.
                                     (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                     is_int a \<Longrightarrow>
                                     \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(b))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(subst including_out2) apply(simp add: S_def a_int b_int del: OclIncluding_commute)+
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule i_cons_all_def, rule including_commute3[THEN c0_of_c], simp add: a_int, simp add: S_def)
  apply(rule all_defined1, rule cons_all_def, simp add: S_def, simp add: int_is_valid[OF a_int], simp add: int_is_valid[OF b_int])

  apply(rule iterate_including_id_out) apply(simp add: S_def a_int)+
 done
qed

lemma iterate_including_id_out'''_generic :
 assumes including_commute4 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes including_commute6 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(x))"
 assumes iterate_including_id_out'''' : "\<And>S a b \<tau>.
                                         (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                         is_int a \<Longrightarrow>
                                         is_int b \<Longrightarrow>
                                         \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(b))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
 apply(subst iterate_subst_set0[where G = "\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(b)"])
  apply(simp add: S_def)
  apply(rule including_commute6[THEN c0_of_c], simp add: a_int, simp add: b_int)
  apply(rule including_commute4[THEN c0_of_c], simp add: a_int, simp add: b_int)
  apply(simp)
 apply(rule iterate_including_id_out'''') apply(simp add: S_def a_int b_int)+
done
qed

section{* Conclusion *}

lemma GogollasChallenge_on_sets_generic:
 assumes val_0[simp] : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> zero"
 assumes val_6[simp] : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> six"
 assumes val_8[simp] : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> eight"
 assumes val_9[simp] : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> nine"
 assumes OclInt0_int : "is_int (zero :: ('\<AA>, 'a option option) val)"
 assumes OclInt6_int : "is_int (six :: ('\<AA>, 'a option option) val)"
 assumes OclInt8_int : "is_int (eight :: ('\<AA>, 'a option option) val)"
 assumes OclInt9_int : "is_int (nine :: ('\<AA>, 'a option option) val)"
 assumes including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, 'a option option) Set). r2->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes including_commute2 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)))"
 assumes including_commute3 : "\<And>i. is_int i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). ((acc->including\<^sub>S\<^sub>e\<^sub>t(i))->including\<^sub>S\<^sub>e\<^sub>t(x)))"
 assumes including_commute4 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j))"
 assumes including_commute5 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i))"
 assumes including_commute6 : "\<And>i j. is_int i \<Longrightarrow> is_int j \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, 'a option option) Set). acc->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(x))"
 assumes iterate_including_id : "\<And>(S:: ('\<AA>, 'a option option) Set). (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j))) = S"
 assumes iterate_including_id_out : "\<And>S a \<tau>.
                                     (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                     is_int a \<Longrightarrow>
                                     \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
 assumes iterate_including_id_out' : "\<And>S a \<tau>.
                                      (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                      is_int a \<Longrightarrow>
                                      \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(a))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>"
 assumes iterate_including_id_out''' : "\<And>S a b \<tau>.
                                      (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                      is_int a \<Longrightarrow>
                                      is_int b \<Longrightarrow>
                                      \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b)->including\<^sub>S\<^sub>e\<^sub>t(j))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
 assumes iterate_including_id_out'''' : "\<And>S a b \<tau>.
                                      (\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                                      is_int a \<Longrightarrow>
                                      is_int b \<Longrightarrow>
                                      \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=S | r2->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(b))) \<tau> = S->including\<^sub>S\<^sub>e\<^sub>t(a)->including\<^sub>S\<^sub>e\<^sub>t(b) \<tau>"
 assumes iterate_including_commute_var : "\<And>F a.
            EQ_comp_fun_commute0 (\<lambda>x. (F :: ('\<AA>, 'a option option) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x)) \<Longrightarrow>
            (\<And>x y.
              is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
              is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                  UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). x, a} Set{\<lambda>(_:: '\<AA> st). x, a} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) =
                  UML_Set.OclIterate Set{\<lambda>(_:: '\<AA> st). y, a} Set{\<lambda>(_:: '\<AA> st). y, a} F->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) \<Longrightarrow>
            (\<And>S x y \<tau>.
              is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
              is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
              \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
              \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                  (UML_Set.OclIterate (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y) \<tau> =
                  (UML_Set.OclIterate (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) (((UML_Set.OclIterate S S F)->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). y)) F)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x) \<tau>) \<Longrightarrow>
            is_int a \<Longrightarrow>
            EQ_comp_fun_commute0 (\<lambda>x r1. (((r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | F j r2))->including\<^sub>S\<^sub>e\<^sub>t(a))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x)))"
 assumes including_out0 : "\<And>(S:: ('\<AA>, 'a option option) Set) a. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
          (\<And>\<tau> \<tau>'. S \<tau> = S \<tau>') \<Longrightarrow> (\<And>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {}) \<Longrightarrow> is_int a \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=Set{a} | acc->including\<^sub>S\<^sub>e\<^sub>t(x))) = S->including\<^sub>S\<^sub>e\<^sub>t(a)"
 assumes including_out1 : "\<And>(S:: ('\<AA>, 'a option option) Set) A i \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
          (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
          is_int i \<Longrightarrow>
          \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = S ->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i) \<tau>"
 assumes including_out2 : "\<And>S A i x0 \<tau>.
                           (\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)) \<Longrightarrow>
                           (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
                           is_int i \<Longrightarrow>
                           is_int x0 \<Longrightarrow>
                           \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(i))) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x;acc=A | acc->including\<^sub>S\<^sub>e\<^sub>t(x0)->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau>"
  shows
      "(\<tau>:: '\<AA> st) \<Turnstile> (Set{ six,eight } ->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1=Set{nine}|
                        r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1|
                                    r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)))) \<doteq> Set{zero, six, eight, nine}"
proof -

 have all_defined_68 : "\<And>\<tau>. all_defined \<tau> Set{six, eight}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done
 have all_defined_9 : "\<And>\<tau>. all_defined \<tau> Set{nine}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have commute8: "EQ_comp_fun_commute (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(x))" apply(rule including_commute3) by (simp add: OclInt0_int)
 have commute7: "EQ_comp_fun_commute (\<lambda>x acc. acc->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(zero))" apply(rule including_commute2) by (simp add: OclInt0_int)
 have commute4: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(xa)->including\<^sub>S\<^sub>e\<^sub>t(x))" apply(rule including_commute4) by(simp add: OclInt0_int, blast)
 have commute3: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(x)->including\<^sub>S\<^sub>e\<^sub>t(xa))" apply(rule including_commute6) by(simp add: OclInt0_int, blast)

 have swap1 : "\<And>(S:: ('\<AA>, _) Set) y x.
              is_int x \<Longrightarrow>
              is_int y \<Longrightarrow>
              \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow>
                   ((((S->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(x))->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(y)) =
                   ((((S->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(y))->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(x))"
 by simp

 have commute5: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(j))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x))"
  apply(rule iterate_including_commute, rule commute8[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst UML_Set.OclIncluding.cp0)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  (* *)
   apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric], simp)

  (* *)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) cp_OclIterate1[OF including_commute3[THEN c0_of_c, THEN c0'_of_c0]], simp add: OclInt0_int)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)

  apply(subst (1 2 3 4 5) iterate_including_id_out)

  apply(metis surj_pair, simp add: OclInt0_int, simp)
  apply(subst UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(rule iterate_notempty, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(subst UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute6: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). x))"
  apply(rule iterate_including_commute, rule commute7[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst UML_Set.OclIncluding.cp0)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  (* *)
   apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric], simp)
  (* *)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) cp_OclIterate1[OF including_commute2[THEN c0_of_c, THEN c0'_of_c0]], simp add: OclInt0_int)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)

  apply(subst (1 2 3 4 5) iterate_including_id_out')

  apply(metis surj_pair, simp add: OclInt0_int, simp)
  apply(subst UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(rule iterate_notempty, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(subst UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute9: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(j))->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. x))"
  apply(rule iterate_including_commute_var, rule including_commute[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) iterate_including_id)
   apply (metis OclInt0_int cons_all_def' is_int_def mtSet_all_def)
   apply (metis OclInt0_int cons_all_def' is_int_def mtSet_all_def)

    apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric], simp)
  (* *)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subst (1 2) cp_OclIterate1, rule including_commute[THEN c0_of_c, THEN c0'_of_c0])
   apply(rule cons_all_def')+ apply(rule i_cons_all_def) apply(rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
   apply(rule cons_all_def')+ apply(rule i_cons_all_def) apply(rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)


  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8 9 10) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5) iterate_including_id)

  apply(metis surj_pair)
  apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule cons_all_def', rule i_cons_all_def, rule including_commute[THEN c0_of_c], metis surj_pair) apply(simp add: int_is_valid)+
  apply(subst (1 2) UML_Set.OclIncluding.cp0[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule cons_all_def', metis surj_pair) apply(simp add: int_is_valid)+ apply(metis surj_pair)

  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6) UML_Set.OclIncluding.cp0[symmetric])
  apply(simp add: int_is_valid OclInt0_int)+
 done

 have commute1: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>)->including\<^sub>S\<^sub>e\<^sub>t(j)))"
  apply(rule iterate_commute')
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate1)
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
  apply(subst (1 2 3 4 5) iterate_including_id_out''')
  apply(simp_all add: OclInt0_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute5[THEN c0_of_c], simp add: OclInt0_int, simp add: OclInt0_int)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute5[THEN c0_of_c], simp, simp add: OclInt0_int)
   apply(metis surj_pair)
   apply(simp)
  apply(subst cp_all_def[symmetric])
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(subst (1 2 3 4) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute2: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>)))"
  apply(rule iterate_commute')
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate1)
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
  apply(subst (1 2 3 4 5) iterate_including_id_out'''')
  apply(simp_all add: OclInt0_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute5[THEN c0_of_c], simp, simp add: OclInt0_int)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute5[THEN c0_of_c], simp, simp add: OclInt0_int)
   apply(metis surj_pair)
   apply(simp)
  apply(subst cp_all_def[symmetric])
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(subst (1 2 3 4) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0)
  apply(subst (1 2 3 4 5 6 7 8) UML_Set.OclIncluding.cp0[symmetric])
  apply(subst swap1, simp_all)
 done

 have set68_notempty : "\<And>(\<tau>:: '\<AA> st). \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Set{six, eight} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty)
  apply(simp add: mtSet_all_def)
  apply(simp add: int_is_valid)
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set9_notempty : "\<And>(\<tau>:: '\<AA> st). \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Set{nine} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set68_cp : "\<And>(\<tau>:: '\<AA> st) (\<tau>':: '\<AA> st). Set{six, eight} \<tau> = Set{six, eight} \<tau>'"
  apply(rule including_cp_all) apply(simp add: OclInt6_int) apply(simp add: mtSet_all_def)
  apply(rule including_cp_all) apply(simp add: OclInt8_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)
 have set9_cp : "\<And>(\<tau>1:: '\<AA> st) (\<tau>2:: '\<AA> st). Set{nine} \<tau>1 = Set{nine} \<tau>2"
  apply(rule including_cp_all) apply(simp add: OclInt9_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)

 note iterate_subst_set___ = iterate_subst_set___[OF all_defined_68 all_defined_9 set9_cp _ _ _ set9_notempty]
 note iterate_subst_set''0 = iterate_subst_set''0[OF all_defined_68 all_defined_9 _ _ _ set9_notempty]
 note iterate_subst_set'0 = iterate_subst_set'0[OF all_defined_68 all_defined_9 set9_cp]

 have GogollasChallenge_on_sets:
      "(Set{ six,eight } ->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1=Set{nine}|
                        r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1|
                                    r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)))) \<tau> = Set{zero, six, eight, nine} \<tau>"
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i))"])
   apply(simp add: commute1 del: OclIncluding_commute, simp add: commute2 del: OclIncluding_commute)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. \<lfloor>x\<rfloor>)"]) apply(blast)+
   apply(simp add: commute3 del: OclIncluding_commute, simp add: commute4 del: OclIncluding_commute)
   apply(simp)
   apply(simp add: int_is_valid del: OclIncluding_commute)+
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(j))->including\<^sub>S\<^sub>e\<^sub>t(i)"])
   apply(simp add: commute2 del: OclIncluding_commute, simp add: commute5[THEN c0'_of_c0] del: OclIncluding_commute)
  apply(rule including_out2)
   apply(blast) apply(blast) apply(blast) apply(simp add: OclInt0_int) apply(simp)
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(zero))->including\<^sub>S\<^sub>e\<^sub>t(i)"])
   apply(simp add: commute5[THEN c0'_of_c0] del: OclIncluding_commute, simp add: commute6[THEN c0'_of_c0] del: OclIncluding_commute)
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(simp add: int_is_valid)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(zero)"]) apply(blast)+
   apply(simp add: commute8 del: OclIncluding_commute, simp add: commute7 del: OclIncluding_commute)
  apply(simp)
   apply(simp add: all_defined1)
  (* *)
  apply(subst iterate_subst_set''0[where G = "\<lambda>i r1. r1 ->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1 | r2->including\<^sub>S\<^sub>e\<^sub>t(j))->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(i)"])
   apply(simp add: commute6, simp add: commute9)
  apply(rule including_subst_set'')
   apply(rule all_defined1) apply(rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(rule all_defined1) apply(rule cons_all_def, rule i_cons_all_def, rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
  apply(rule including_out1)
   apply(blast) apply(blast) apply(simp add: OclInt0_int) apply(simp)
  (* *)
  apply(subst iterate_subst_set'0[where G = "\<lambda>i r1. r1->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(i)"])
   apply(simp add: commute9, simp add: commute8[THEN c0_of_c])
  apply(rule including_subst_set)+
  apply(rule iterate_including_id) apply(blast)+
  (* *)
  apply(subst iterate_subst_set[where G = "\<lambda>i r1. r1->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(zero)"])
   apply(simp add: all_defined_68, simp add: all_defined_9, simp add: commute8 del: OclIncluding_commute, simp add: commute7 del: OclIncluding_commute)
  apply(simp)
  (* *)
  apply(subst including_out1[OF all_defined_68 all_defined_9 OclInt0_int set68_notempty])
  (* *)
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def'', rule including_commute[THEN c0_of_c, THEN c0'_of_c0], simp add: all_defined_68, simp add: all_defined_9)
   apply (metis "UML_Set.OclIncluding.1" OclANY_singleton_exec OclANY_valid_args_valid'' OclInt6_int OclInt8_int OclInt9_int UML_Set.OclIncluding.def_valid_then_def int_is_valid)
   apply(simp)
  (* *)
  apply(subst including_out0[OF all_defined_68 set68_cp set68_notempty OclInt9_int])
  (* *)
 by(simp)

 have valid_1 : "\<tau> \<Turnstile> \<upsilon> (Set{ six,eight } ->iterate\<^sub>S\<^sub>e\<^sub>t(i;r1=Set{nine}|
                        r1->iterate\<^sub>S\<^sub>e\<^sub>t(j;r2=r1|
                                    r2->including\<^sub>S\<^sub>e\<^sub>t(zero)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j))))"
 by(rule foundation20, rule all_defined1, rule i_cons_all_def'', rule commute1, rule all_defined_68, rule all_defined_9)

 have valid_2 : "\<tau> \<Turnstile> \<upsilon> Set{zero, six, eight, nine}"
  apply(rule foundation20, rule all_defined1) apply(rule cons_all_def)+
  apply(simp_all add: mtSet_all_def)
 done

 show ?thesis
  apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def StrongEq_def valid_1[simplified OclValid_def] valid_2[simplified OclValid_def] del: OclIncluding_commute)
  apply(simp add: GogollasChallenge_on_sets true_def del: OclIncluding_commute)
 done
qed

section{* OCL lib (continued) *} (* OCL_lib *)

lemma OclSelect_body_commute :
 shows "comp_fun_commute (OclSelect_body (P::(('\<AA> state \<times> '\<AA> state \<Rightarrow> 'a option option)
    \<Rightarrow> '\<AA> state \<times> '\<AA> state \<Rightarrow> bool option option)))"
proof -
 have cp_OclIncluding1: "\<And>x S \<tau>. S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau> = \<lambda>_. S \<tau>->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>"
 by(simp only: UML_Set.OclIncluding_def, subst cp_defined, simp)
 show ?thesis
  apply(simp add: OclSelect_body_def)
  apply(rule if_commute_gen_var_gen)
  apply(rule including_commute0_generic)
  apply(simp add: comp_fun_commute_def)+
  apply(rule cp_OclIncluding1)
 by(simp)+
qed

lemma select_iterate:
 assumes OclSelect_body_commute : "comp_fun_commute (OclSelect_body (P::(('\<AA> state \<times> '\<AA> state \<Rightarrow> 'a option option)
    \<Rightarrow> '\<AA> state \<times> '\<AA> state \<Rightarrow> bool option option)))"
 assumes S_finite: "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
     and P_strict: "\<And>x. x \<tau> = \<bottom> \<Longrightarrow> (P x) \<tau> = \<bottom>"
   shows "UML_Set.OclSelect S P \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x; acc = Set{} | OclSelect_body P x acc)) \<tau>"
proof -
 have ex_insert : "\<And>x F P. (\<exists>x\<in>insert x F. P x) = (P x \<or> (\<exists>x\<in>F. P x))"
 by (metis insert_iff)

 have insert_set : "\<And>s P S. \<not> P s \<Longrightarrow> {x \<in> insert s S. P x} = {x \<in> S. P x}"
 by (metis (mono_tags) insert_iff)

 have inj : "\<And>x F. x \<notin> F \<Longrightarrow> (\<lambda>\<tau>. x) \<notin> (\<lambda>a \<tau>. a) ` F"
 by (metis image_iff)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
 by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have not_strongeq : "\<And>P. P \<tau> \<noteq> invalid \<tau> \<Longrightarrow> \<not> \<tau> \<Turnstile> P \<doteq> false \<Longrightarrow> (P \<doteq> false) \<tau> = false \<tau>"
 by (metis (hide_lams, no_types) OclValid_def StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.defined_args_valid bool_split_0 foundation1 foundation16 foundation18 invalid_def null_fun_def valid4)


 show ?thesis
  apply(simp add: OclSelect_body_def)
  apply(simp only: UML_Set.OclSelect_def UML_Set.OclIterate_def)
  apply(case_tac "\<tau> \<Turnstile> \<delta> S", simp only: OclValid_def)
  apply(subgoal_tac "(if \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = invalid \<tau> then invalid \<tau>
          else Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}\<rfloor>\<rfloor>) =
          Finite_Set.fold (OclSelect_body P) Set{}
           ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<tau>",
        simp add: S_finite)
  apply(rule finite_induct[where P = "\<lambda>set. (if \<exists>x\<in>set. P (\<lambda>_. x) \<tau> = invalid \<tau> then invalid \<tau>
     else Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> set. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}\<rfloor>\<rfloor>) =
    Finite_Set.fold (OclSelect_body P) Set{}
     ((\<lambda>a \<tau>. a) ` set) \<tau>", OF S_finite])
  apply(simp add: mtSet_def)
  (* *)
  apply(simp only: image_insert)
  apply(subst comp_fun_commute.fold_insert[OF OclSelect_body_commute], simp)
  apply(rule inj, fast)

  apply(simp only: OclSelect_body_def)
  apply(simp only: ex_insert)
  apply(subst cp_OclIf)
  apply(case_tac "\<not> ((\<upsilon> (P (\<lambda>_. x))) \<tau> = true \<tau>)")
  apply(drule valid_inject_true)
  apply(subgoal_tac "P (\<lambda>_. x) \<tau> = invalid \<tau>", simp add: cp_OclIf[symmetric], simp add: bot_fun_def invalid_def)
  apply(simp add: OclIf_def StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n false_def true_def invalid_def bot_option_def StrongEq_def defined_def bot_Boolean_def)
  apply (metis bot_fun_def OclValid_def foundation2 valid_def invalid_def)

  apply(subst cp_OclIf)
  apply(subgoal_tac "P (\<lambda>_. x) \<tau> \<noteq> invalid \<tau>")
  prefer 2
  apply (metis bot_fun_def OclValid_def foundation2 valid_def invalid_def)

  apply(case_tac "\<tau> \<Turnstile> (P (\<lambda>_. x) \<doteq> false)")
  apply(subst insert_set, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def, metis OclValid_def foundation22)

  apply(simp add: cp_OclIf[symmetric])
  (* *)
  apply(subst not_strongeq, simp, simp)

  apply(simp add: cp_OclIf[symmetric])
  apply(drule sym, drule sym) (* SYM 1/2 *)
  apply(subst (1 2) UML_Set.OclIncluding.cp0)
  apply(subgoal_tac "((\<lambda>_. Finite_Set.fold (OclSelect_body P) Set{} ((\<lambda>a \<tau>. a) ` F) \<tau>)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x)) \<tau>
                     =
                     ((\<lambda>_. if \<exists>x\<in>F. P (\<lambda>_. x) \<tau> = invalid \<tau> then invalid \<tau> else Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}\<rfloor>\<rfloor>)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. x)) \<tau>")
   prefer 2
   apply(simp add: OclSelect_body_def)
  apply(simp add: )

  apply(rule conjI)
  apply (metis (no_types, lifting) OclValid_def UML_Set.OclIncluding_def defined_def invalid_set_OclNot_defined not_strongeq)

  apply(rule impI, subst UML_Set.OclIncluding_def, subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def null_option_def)
  apply(rule allI, rule impI)
  apply(subgoal_tac "xa \<noteq> \<bottom>", case_tac xa, simp add: bot_option_def, simp)
  apply (metis (no_types) bot_fun_def P_strict invalid_def)
  apply(simp)

  apply(drule sym, simp only:, drule sym, simp only:) (* SYM 2/2 *)
  apply(subst (1 2) defined_def, simp add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def false_def true_def null_fun_def bot_fun_def)

  apply(subgoal_tac "(\<upsilon> (\<lambda>_. x)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>")
   prefer 2
   proof - fix x show "(\<upsilon> P (\<lambda>_. x)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Longrightarrow> (\<upsilon> (\<lambda>_. x)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
   by (metis bot_fun_def P_strict true_def valid_def)
  apply_end(subgoal_tac "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None \<and> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>", simp)
  apply_end(subgoal_tac "{xa. (xa = x \<or> xa \<in> F) \<and> P (\<lambda>_. xa) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>} = insert x {x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>}", simp)
  apply_end(rule equalityI)
  apply_end(rule subsetI, simp)
  apply_end(rule subsetI, simp, simp add: OclValid_def StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n true_def StrongEq_def, blast)


  fix F
  show "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None \<and> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x \<in> F. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
    when "\<forall>x\<in>F. P (\<lambda>_. x) \<tau> \<noteq> \<bottom>"
   apply(insert that, subst (1 2) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, simp_all add: bot_option_def null_option_def)
   apply(rule allI, rule impI)
   proof - fix x show "\<forall>x\<in>F. \<exists>y. P (\<lambda>_. x) \<tau> = \<lfloor>y\<rfloor> \<Longrightarrow> x \<in> F \<and> P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Longrightarrow> \<exists>y. x = \<lfloor>y\<rfloor>"
    apply(case_tac "x = \<bottom>", drule P_strict[where x = "\<lambda>_. x"])
    apply(drule_tac x = x in ballE) prefer 3 apply assumption
    apply(simp add: bot_option_def)+
   done
  qed
  apply_end(simp add: OclValid_def invalid_def)+
 qed
qed

end
