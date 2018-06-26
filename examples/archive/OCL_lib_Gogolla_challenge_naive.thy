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
  OCL_lib_Gogolla_challenge_naive
imports
  Isabelle_Finite_Set
begin

no_notation None ("\<bottom>")

text{* As illustration, we present several naive lemmas, that can be proved but will not be used,
since they have @{term "comp_fun_commute F"} as hypothesis: *}

lemma (*OclIterate_valid:*)
assumes S_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
and F_commute: "comp_fun_commute F"
and F_valid_arg: "\<And>a A. \<upsilon> (F a A) = (\<upsilon> a and \<upsilon> A)"
shows   "\<upsilon> (S->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | F a x)) = (\<delta> S and (S->forAll\<^sub>S\<^sub>e\<^sub>t(x | \<upsilon> x)) and \<upsilon> A)"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
  apply(simp add: defined_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom>", simp_all add: true_def)

 have contradict_Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e: "\<And>\<tau> S f.
         \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. f (\<lambda>_. x) \<tau> \<Longrightarrow>
         \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>) \<Longrightarrow>
         False"
  apply(drule bexE[where Q = False])
   apply(drule bspec)
    apply(assumption)
 by(simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have fold_exec_true : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           (\<delta> S) \<tau> = true \<tau> \<Longrightarrow>
           (\<upsilon> A) \<tau> = true \<tau> \<Longrightarrow>
           (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>) \<Longrightarrow>
           ((\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = true \<tau>)"
 proof -
  fix \<tau>
  show "(\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
             (\<delta> S) \<tau> = true \<tau> \<Longrightarrow>
             (\<upsilon> A) \<tau> = true \<tau> \<Longrightarrow>
             (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>) \<Longrightarrow> ?thesis \<tau>"

  apply(case_tac "\<exists>x. x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp_all)
  apply(drule exE) prefer 2 apply(assumption)

  apply(subst finite_induct[where P = "\<lambda>set. (\<forall>x\<in>set. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>) -->  (\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set)) \<tau> = true \<tau>"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"])
      apply(simp)
     apply(simp)
     defer
    apply(simp)
   apply(simp)
  apply(rule impI)+
  apply(simp, erule conjE)
  apply(subgoal_tac "\<exists>x. Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) = x \<and> (\<upsilon> x) \<tau> = true \<tau>")
   prefer 2
   apply(rule_tac x = "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)" in exI)
   apply(simp)
  apply(drule exE) prefer 2 apply(assumption)
  apply(drule conjE) prefer 2 apply(assumption)
  apply(subgoal_tac "F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) = F (\<lambda>\<tau>. xa) xb")
   prefer 2
   apply(simp)
  apply(subst comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. xa)"])
     apply(rule F_commute)
    apply(simp)
   apply(rule image_cong)
    apply(rule inject)
   apply(simp)
  apply(simp)
  apply(subst F_valid_arg)
  apply(simp add: cp_OclAnd)
  done
 qed

 have fold_exec_false : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           (\<delta> S) \<tau> = true \<tau> \<Longrightarrow>
           (\<upsilon> A) \<tau> = true \<tau> \<Longrightarrow>
           (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = false \<tau>) \<Longrightarrow>
           ((\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = false \<tau>)"
 proof -
  fix \<tau>
  show "(\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
            (\<delta> S) \<tau> = true \<tau> \<Longrightarrow>
            (\<upsilon> A) \<tau> = true \<tau> \<Longrightarrow>
            (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = false \<tau>) \<Longrightarrow> ?thesis \<tau>"

  apply(case_tac "\<exists>x. x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp_all)
  apply(drule exE) prefer 2 apply(assumption)

  apply(subst finite_induct[where P = "\<lambda>set. (\<exists>x\<in>set. (\<upsilon> (\<lambda>_. x)) \<tau> = false \<tau>) -->  (\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set)) \<tau> = false \<tau>"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"])
      apply(simp)
     apply(simp)
     defer
    apply(simp)
   apply(simp)
  apply(rule impI)+
  apply(drule_tac A = "insert xa Fa" in bexE) prefer 2 apply(assumption)
  apply(simp, drule disjE) prefer 3 apply(assumption)
   apply(simp)
   apply(subgoal_tac "\<forall>x. Finite_Set.fold F A (insert (\<lambda>\<tau>. xa) ((\<lambda>a \<tau>. a) ` Fa)) = x \<longrightarrow> (\<upsilon> x) \<tau> = false \<tau>") apply(simp, rule allI, rule impI)
   apply(subgoal_tac "F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) = xc")
    prefer 2
    apply(subst comp_fun_commute.fold_insert[where f = F and z = A and x = "(\<lambda>\<tau>. xa)" and A = "((\<lambda>a \<tau>. a) ` Fa)", symmetric])
       apply(rule F_commute)
      apply(simp)
      apply(rule image_cong)
     apply(rule inject)
    apply(simp)
   apply(simp)
   apply(subgoal_tac "(\<upsilon> (F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)))) \<tau> = false \<tau>") apply(simp)
   apply(subst F_valid_arg)
   apply(subst cp_OclAnd[where X = "\<upsilon> (\<lambda>\<tau>. xa)"], simp)
   apply(simp add: cp_OclAnd[symmetric])

  apply(auto)
  apply(subgoal_tac "\<exists>x. Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) = x \<and> (\<upsilon> x) \<tau> = false \<tau>")
   prefer 2
   apply(rule_tac x = "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)" in exI)
   apply(simp)
  apply(drule exE) prefer 2 apply(assumption)
  apply(drule conjE) prefer 2 apply(assumption)
  apply(subgoal_tac "F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) = F (\<lambda>\<tau>. xa) xd")
   prefer 2
   apply(simp)
  apply(subst comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. xa)"])
     apply(rule F_commute)
    apply(simp)
    apply(rule image_cong)
    apply(rule inject)
   apply(simp)
  apply(simp)
  apply(subst F_valid_arg)
  apply(subst cp_OclAnd[where X = "\<upsilon> (\<lambda>\<tau>. xa)"])
  apply(simp add: cp_OclAnd[symmetric])
  done
 qed

 have fold_exec : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           (\<delta> S) \<tau> = true \<tau> \<Longrightarrow>
           (\<upsilon> A) \<tau> = true \<tau> \<Longrightarrow>
           (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>) = ((\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = true \<tau>)"
  apply(case_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>")
  apply(simp add: fold_exec_true)

  apply(simp)
  apply(subgoal_tac "(\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> = false \<tau>")
   prefer 2
   apply(rule fold_exec_false, simp_all)
   apply(drule bexE) prefer 2 apply(assumption)
   apply(rule_tac x = x in bexI) apply(rule valid_inject_true, simp_all)

   apply(auto)
 done

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(simp add: cp_valid[of "UML_Set.OclIterate S A F"])
  apply(simp add: UML_Set.OclIterate_def)
  apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
  apply(simp add: cp_OclAnd[symmetric] cp_valid[symmetric])
  apply(insert S_finite, simp)

  apply(rule conjI)
   prefer 2
   apply(case_tac "(\<upsilon> A) \<tau> = true \<tau>", simp)

    apply(rule impI)
    apply(subgoal_tac "(\<delta> S) \<tau> = false \<tau>")
     prefer 2
     apply(rule defined_inject_true)
     apply(simp)
    apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
    apply(simp add: cp_OclAnd[symmetric])
    apply(simp add: valid_def bot_fun_def)

   apply(subgoal_tac "(\<upsilon> A) \<tau> = false \<tau>")
    prefer 2
    apply(rule valid_inject_true)
    apply(simp)
   apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
   apply(simp add: cp_OclAnd[symmetric])
   apply(simp add: valid_def bot_fun_def)

  apply(rule impI, erule conjE)

  apply(case_tac "\<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)")
   apply(drule fold_exec[symmetric], simp_all add: OclValid_def)
   apply(simp add: UML_Set.OclForall_def)

  apply(drule valid_inject_true)
  apply(drule fold_exec[symmetric], simp_all add: OclValid_def)
  apply(simp add: UML_Set.OclForall_def)

  by (metis bot_fun_def valid_def)
qed

lemma (*OclIterate\<^sub>S\<^sub>e\<^sub>t_valid_:*)
assumes S_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
and F_commute: "comp_fun_commute F"
and A_defined: "\<delta> A = \<upsilon> A"
and F_defined: "\<And>a A. \<delta> A = \<upsilon> A \<Longrightarrow> \<delta> (F a A) = \<upsilon> (F a A)"
(*and F_valid_arg: "\<And>a A. \<upsilon> (F a A) = (\<upsilon> a and \<upsilon> A)"*)
and F_valid_arg_true: "\<And>\<tau> a A. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<delta> A \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (F a A)"
and F_valid_arg_false1: "\<And>\<tau> a A. \<not> (\<tau> \<Turnstile> \<upsilon> a) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon> (F a A))"
and F_valid_arg_false2: "\<And>\<tau> a A. \<not> (\<tau> \<Turnstile> \<upsilon> A) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon> (F a A))"
shows   "\<upsilon> (S->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | F a x)) = (\<delta> S and (S->forAll\<^sub>S\<^sub>e\<^sub>t(x | \<upsilon> x)) and \<upsilon> A)"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
  apply(simp add: defined_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom>", simp_all add: true_def)

 have contradict_Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e: "\<And>\<tau> S f.
         \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. f (\<lambda>_. x) \<tau> \<Longrightarrow>
         \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>) \<Longrightarrow>
         False"
  apply(drule bexE[where Q = False])
   apply(drule bspec)
    apply(assumption)
 by(simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have fold_exec_true : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           \<tau> \<Turnstile> \<delta> S \<Longrightarrow>
           \<tau> \<Turnstile> \<upsilon> A \<Longrightarrow>
           (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))) \<Longrightarrow>
           \<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"

  apply(case_tac "\<exists>x. x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp_all)
  apply(drule exE) prefer 2 apply(assumption)

  apply(subst finite_induct[where P = "\<lambda>set. (\<forall>x\<in>set. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))) -->  (\<tau> \<Turnstile> \<upsilon> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set)))"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"])
      apply(simp)
     apply(simp)
    defer
    apply(simp)
   apply(simp)
  apply(rule impI)+
  apply(simp, erule conjE)
  apply(subgoal_tac "\<exists>x. Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) = x \<and> (\<tau> \<Turnstile> \<upsilon> x)")
   prefer 2
   apply(rule_tac x = "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)" in exI)
   apply(simp)
  apply(drule exE) prefer 2 apply(assumption)
  apply(drule conjE) prefer 2 apply(assumption)
  apply(subgoal_tac "F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) = F (\<lambda>\<tau>. xa) xb")
   prefer 2
   apply(simp)
  apply(subst comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. xa)"])
     apply(rule F_commute)
    apply(simp)
   apply(rule image_cong)
    apply(rule inject)
   apply(simp)
  apply(simp)
  apply(subst F_valid_arg_true, simp_all)

  apply(subgoal_tac "\<upsilon> xb = \<delta> xb", simp)

  apply(subgoal_tac "let c = Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) in \<upsilon> c = \<delta> c", simp)

  apply(subst finite_induct[where P = "\<lambda>set. let c = Finite_Set.fold F A set in \<upsilon> c = \<delta> c"
                              and F = "(\<lambda>a \<tau>. a) ` Fa"])
     apply(simp)
    apply(simp)
    apply(insert A_defined, simp)
   defer
   apply(simp)
  apply(subst comp_fun_commute.fold_insert)
     apply(rule F_commute)
    apply(simp)
   apply(simp)
  apply(simp add: Let_def)
  apply(subst F_defined)
   apply(simp)+
 done

 have fold_exec_false : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           \<tau> \<Turnstile> (\<delta> S) \<Longrightarrow>
           \<tau> \<Turnstile> (\<upsilon> A) \<Longrightarrow>
           (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. \<not> (\<tau> \<Turnstile> (\<upsilon> (\<lambda>_. x)))) \<Longrightarrow>
           \<not> (\<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))"

  apply(case_tac "\<exists>x. x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>", simp_all)
  apply(drule exE) prefer 2 apply(assumption)

  apply(subst finite_induct[where P = "\<lambda>set. (\<exists>x\<in>set. \<not> (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))) --> \<not> (\<tau> \<Turnstile> (\<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set)))"
                              and F = "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"])
      apply(simp)
     apply(simp)
    defer
    apply(simp)
   apply(simp)
  apply(rule impI)+

  apply(drule_tac A = "insert xa Fa" in bexE) prefer 2 apply(assumption)
  apply(simp, drule disjE) prefer 3 apply(assumption)
   apply(simp)
   apply(subgoal_tac "\<forall>x. Finite_Set.fold F A (insert (\<lambda>\<tau>. xa) ((\<lambda>a \<tau>. a) ` Fa)) = x \<longrightarrow> \<not> (\<tau> \<Turnstile> (\<upsilon> x))") apply(simp, rule allI, rule impI)
   apply(subgoal_tac "F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) = xc")
    prefer 2
    apply(subst comp_fun_commute.fold_insert[where f = F and z = A and x = "(\<lambda>\<tau>. xa)" and A = "((\<lambda>a \<tau>. a) ` Fa)", symmetric])
       apply(rule F_commute)
      apply(simp)
     apply(rule image_cong)
      apply(rule inject)
     apply(simp)
    apply(simp)
   apply(subgoal_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> (F (\<lambda>\<tau>. xa) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)))))") apply(simp)
   apply(rule F_valid_arg_false1, simp)

  apply(subst comp_fun_commute.fold_insert[where f = F and z = A and x = "(\<lambda>\<tau>. xa)" and A = "((\<lambda>a \<tau>. a) ` Fa)"])
     apply(rule F_commute)
    apply(simp)
    apply(rule image_cong)
    apply(rule inject)
   apply(simp)
  apply(rule F_valid_arg_false2)
  apply(subgoal_tac "\<exists>x\<in>Fa. \<not> (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))", simp)
  apply(rule_tac x = xb in bexI, simp_all)
 done

 have fold_exec : "\<And>\<tau>. (\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
           \<tau> \<Turnstile> (\<delta> S) \<Longrightarrow>
           \<tau> \<Turnstile> (\<upsilon> A) \<Longrightarrow>
           (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))) = (\<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))"
  apply(case_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))")
   apply(simp add: fold_exec_true)

  apply(simp)
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))")
   prefer 2
   apply(rule fold_exec_false, simp_all)
 done

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_false_bot : "\<And>\<tau>. (false \<tau> = bot \<tau>) = False" by (metis defined4 defined_def discr_eq_false_true)
 have discr_eq_false_null : "\<And>\<tau>. (false \<tau> = null \<tau>) = False" by (metis defined4 defined_def discr_eq_false_true)
 have e_valid_inject_true : "\<And>\<tau>. \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> \<noteq> true \<tau> \<Longrightarrow> \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = false \<tau>"
 by (metis valid_inject_true)
 have f_valid_inject_true : "\<And>\<tau>. \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> \<noteq> false \<tau> \<Longrightarrow> \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>"
 by (metis valid_inject_true)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(simp add: cp_valid[of "UML_Set.OclIterate S A F"])
  apply(simp add: UML_Set.OclIterate_def)
  apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
  apply(simp add: cp_OclAnd[symmetric] cp_valid[symmetric])
  apply(insert S_finite, simp)

  apply(rule conjI)
   prefer 2
   apply(case_tac "\<tau> \<Turnstile> (\<upsilon> A)", simp add: OclValid_def)

    apply(rule impI)
    apply(subgoal_tac "\<not> (\<tau> \<Turnstile> (\<delta> S))")
     prefer 2
     apply(simp add: OclValid_def)
    apply(drule defined_inject_true)
    apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
    apply(simp add: cp_OclAnd[symmetric])
    apply(simp add: valid_def bot_fun_def)

   apply(simp add: OclValid_def)
   apply(drule valid_inject_true)
   apply(simp add: cp_OclAnd[of _ "\<upsilon> A"] cp_OclAnd[of "\<delta> S" ])
   apply(simp add: cp_OclAnd[symmetric])
   apply(simp add: valid_def bot_fun_def)

  apply(rule impI, erule conjE)

  apply(case_tac "\<tau> \<Turnstile> \<upsilon> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)")
   apply(drule fold_exec[symmetric], simp_all add: OclValid_def)
   apply(simp add: UML_Set.OclForall_def)

  apply(drule valid_inject_true)
  apply(drule fold_exec[symmetric], simp_all add: OclValid_def)
  apply(simp add: UML_Set.OclForall_def)

  by (metis bot_fun_def valid_def)
qed

section \<open>...\<close>

lemma mtSet_eq_exec:
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> Set(\<langle>\<langle>int\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>))"
   shows "(S = Set{}) = (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {})"
proof -
 have S_incl : "(\<forall>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {}) \<Longrightarrow> Set{} = S"
  apply(rule ext, rename_tac \<tau>)
  proof - fix \<tau> show "\<forall>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {} \<Longrightarrow> Set{} \<tau> = S \<tau>"
   apply(insert S_all_def[of \<tau>])
   apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
   apply(simp add: mtSet_def)
  by (metis abs_rep_simp' all_defined_def)
 qed
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)

 show ?thesis
  apply(rule iffI)
   apply(rule allI, simp add: mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse B)
  apply(simp add: S_incl)
 done
qed

lemma mtSet_neq_exec :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> Set(\<langle>\<langle>int\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>))"
   shows "(S \<noteq> Set{}) = (\<exists>\<tau>. \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {})"
by(simp add: mtSet_eq_exec[OF S_all_def])

end
