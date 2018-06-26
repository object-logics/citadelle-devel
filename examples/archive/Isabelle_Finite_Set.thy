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
  Isabelle_Finite_Set
imports
  "../../src/collection_types/UML_Set"
begin

no_notation None ("\<bottom>")

section{* Introduction *}

definition "is_int x \<equiv> \<forall> \<tau>. \<tau> \<Turnstile> \<upsilon> x \<and> (\<forall>\<tau>0. x \<tau> = x \<tau>0)"

lemma int_is_valid : "is_int x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
by (metis foundation18' is_int_def)

lemma int_is_const : "is_int x \<Longrightarrow> const x"
by(simp add: is_int_def const_def)

definition "all_int_set S \<equiv> finite S \<and> (\<forall>x\<in>S. is_int x)"
definition "all_int \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_int_set \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
definition "all_defined_set \<tau> S \<equiv> finite S \<and> (\<forall>x\<in>S. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x)))"
definition "all_defined_set' \<tau> S \<equiv> finite S"
definition "all_defined \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_defined_set' \<tau> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"

lemma all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> S \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)"
 apply(simp add: all_defined_def, erule conjE, frule Set_inv_lemma)
 apply(simp add: all_defined_def all_defined_set'_def all_int_set_def is_int_def defined_def OclValid_def)
by (metis (no_types) OclValid_def foundation18' true_def Set_inv_lemma')

term "all_defined \<tau> (f \<zero> Set{\<zero>}) = (all_defined \<tau> Set{\<zero>})"
 (* we check here that all_defined could at least be applied to some useful value
    (i.e. we examine the type of all_defined) *)

lemma int_trivial : "is_int (\<lambda>_. \<lfloor>a\<rfloor>)" by(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)

lemma EQ_sym : "(x::(_, _) Set) = y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<doteq> y)"
by (metis (hide_lams, no_types) OclIf_true' OclValid_def StrictRefEq\<^sub>S\<^sub>e\<^sub>t.refl_ext)

lemma cp_all_def : "all_defined \<tau> f = all_defined \<tau>' (\<lambda>_. f \<tau>)"
  apply(simp add: all_defined_def all_defined_set'_def OclValid_def)
  apply(subst cp_defined)
by (metis (no_types) OclValid_def foundation16)

lemma cp_all_def' : "(\<forall>\<tau>. all_defined \<tau> f) = (\<forall>\<tau> \<tau>'. all_defined \<tau>' (\<lambda>_. f \<tau>))"
 apply(rule iffI)
 apply(rule allI) apply(erule_tac x = \<tau> in allE) apply(rule allI)
 apply(simp add: cp_all_def[THEN iffD1])
 apply(subst cp_all_def, blast)
done

lemma destruct_int' : "const i \<Longrightarrow> \<exists>! j. i = (\<lambda>_. j)"
 proof - fix \<tau> assume "const i" thus ?thesis
  apply(rule_tac a = "i \<tau>" in ex1I)
 by(rule ext, (simp add: const_def)+)
qed

lemma destruct_int : "is_int i \<Longrightarrow> \<exists>! j. i = (\<lambda>_. j)"
by(rule destruct_int', simp add: int_is_const)

section{* Definition: comp fun commute *}

text{* This part develops an Isabelle locale similar as @{term comp_fun_commute},
but containing additional properties on arguments such as definedness, finiteness, non-emptiness... *}

subsection{* Main *}

text{* The iteration with @{term UML_Set.OclIterate} (performed internally through @{term Finite_Set.fold_graph})
accepts any OCL expressions in its polymorphic arguments.
However for @{term UML_Set.OclIterate} to be a congruence where rewriting could cross
several nested @{term UML_Set.OclIterate},
we only focus on a particular class of OCL expressions: ground sets with well-defined properties
like validity, not emptiness, finiteness...
Since the first hypothesis of @{text comp_fun_commute.fold_insert} is too general,
in order to replace it by another weaker locale we have the choice between
reusing the @{term comp_fun_commute} locale or whether completely defining a new locale.
Because elements occurring in the type of @{term Finite_Set.fold_graph} are represented in polymorphic form,
the folding on a value-proposition couple would be possible in a type system with dependent types.
But without the dependent typing facility, we choose to give the well-defined properties
to each functions in a duplicated version of @{term comp_fun_commute}. *}

text{* A first attempt for defining such locale would then be:
\begin{verbatim}
locale EQ_comp_fun_commute =
  fixes f :: "('a state \<times> 'a state \<Rightarrow> int option option)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_S : "\<And>x. cp (f x)"
  assumes cp_x : "\<And>S. cp (\<lambda>x. f x S)"
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. is_int x \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<lceil>\<lceil>@{text "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e"} (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>@{text "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e"} (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>(x:: 'a state \<times> 'a state \<Rightarrow> int option option) y. all_defined \<tau> (f x y) = (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"
  assumes commute: "
                             \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             all_defined \<tau> S \<Longrightarrow>
                             f y (f x S) \<tau> = f x (f y S) \<tau>"
\end{verbatim} % from r9710

The important hypotheses are the last two.

\begin{itemize}
\item @{term commute} is the commutativity property similar as
@{thm comp_fun_commute.comp_fun_commute} (from @{text comp_fun_commute.comp_fun_commute}),
except that the commuting relation is established on OCL terms
(the \verb|\<tau>| state being visible on both sides of the equality) and
finally all arguments contain a preliminary check of validity or ground situation.

\item @{term all_def} is precisely used for inverting an inductive term of the form @{term "fold_graph f z A y"}
by following the same structure of the proof detailed in @{text comp_fun_commute.fold_graph_insertE_aux}.
As a rewriting rule, @{term all_def} permits the inversion
to preserve the @{term all_defined} property on sets.
\end{itemize}
*}

text{* The resolution of Gogolla's challenge is composed of two separate steps:
\begin{enumerate}
\item Finding the list of rewriting rules to apply from the initial OCL term to the normal form.
\item Every rewriting rules that rewrite under a nested @{term "\<lambda>S A. UML_Set.OclIterate S A F"} term (that rewrite in @{term F}) imply to have proved
the associated @{term "EQ_comp_fun_commute F"} in order to preserve the well-defined properties
while crossing @{term UML_Set.OclIterate}
(@{term F} may contain another @{term UML_Set.OclIterate}).
So this part deals with the proof of every @{term "EQ_comp_fun_commute F"}
appearing as precondition in every rewriting rule of the first step.
\end{enumerate}
More generally, every rewriting rules of step 1 can be decomposed into atomic rules.
By atomic rules, we mean rules where at most one @{term UML_Set.OclIterate} exists
in the left hand side (hence right hand side) of the equation.
Ideally the closure of atomic rules would cover
the necessary space for solving an arbitrary nested @{term UML_Set.OclIterate} expression.

In step 2, for each rewriting rule of step 1,
there is an associated @{term "EQ_comp_fun_commute F"} lemma to prove.
The @{term F} function is precisely the left hand side of
the associated rewriting rule.
So the architecture of this part 2 looks similar as the part 1.
In particular every @{term "EQ_comp_fun_commute"} lemmas could be decomposed into atomic lemmas of the form
@{term "EQ_comp_fun_commute F \<Longrightarrow> EQ_comp_fun_commute (g F)"}
with @{term g} a function containing at most one @{term UML_Set.OclIterate} combinator.

However one corner case arises while proving this last formula.
The naive definition of the @{term "EQ_comp_fun_commute"} locale
we made earlier contains hypotheses where free variables are underspecified.
Indeed, when attempting to prove
@{term "\<And>x y \<tau>. all_defined \<tau> (f x y) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"}
(that comes from @{term all_def}),
we remark for instance that the validity of @{term x} could not be established directly.
*}

text{*
As summary, by introducing @{term "EQ_comp_fun_commute"}
we have initially replaced @{term comp_fun_commute} in order to preserve
the well-defined properties across @{term UML_Set.OclIterate},
however here the same well-defined properties should also be preserved
while proving @{term "EQ_comp_fun_commute"} atomic lemmas.
As solution we propose to refine every hypotheses of @{term "EQ_comp_fun_commute"}
where variables appear.
For instance, for @{term all_def} it means to suppose instead
@{term "\<And>x' y. (\<forall>\<tau>. all_defined \<tau> (f x' y)) = (is_int (\<lambda>(_::'a state \<times> 'a state). x') \<and> (\<forall>\<tau>. all_defined \<tau> y))"}.

The curried form of the @{term x} variable ignoring its state implies to change the type of @{term f}:
we have no more an OCL expression as first argument in @{term f}.

The other difference between the previous @{term all_def} and the current is
the scope of the \verb|\<tau>| quantification.
Indeed, @{text comp_fun_commute.fold_insert} depends on @{text comp_fun_commute.fold_graph_fold}
but this last needs an equality of the form @{term "P = Q"}
with @{term P} and @{term Q} two OCL expressions.
Since OCL expressions are described as functions in our shallow embedding representation,
the previous equality can only be obtained under a particular assumption.
For instance, this oops-unterminated lemma can not be proved: *}
lemma assumes "P \<tau> = R \<tau>"
      assumes "Q \<tau> = R \<tau>"
        shows "P = Q" oops
text{* whereas this one can be (using the extensionality rule): *}
lemma assumes "\<forall>\<tau>. P \<tau> = R \<tau>"
      assumes "\<forall>\<tau>. Q \<tau> = R \<tau>"
        shows "P = Q" by (metis assms(1) assms(2) ext)

(*
(* TODO add some comment on comparison with inductively constructed OCL term *)
(*
inductive EQ1_fold_graph :: "(('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> bool"
 for f and z where
  EQ1_emptyI [intro]: "EQ1_fold_graph f z Set{} z" |
  EQ1_insertI [intro]: "\<not> (\<tau> \<Turnstile> A->includes(x)) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow> all_defined \<tau> A \<Longrightarrow> EQ1_fold_graph f z A y
      \<Longrightarrow> EQ1_fold_graph f z (A->including\<^sub>S\<^sub>e\<^sub>t(x)) (f x y)"

inductive_cases EQ1_empty_fold_graphE [elim!]: "EQ1_fold_graph f z Set{} x"
*)

(*
inductive EQ_fold_graph :: "(('\<AA>, _) val
                              \<Rightarrow> ('\<AA>, _) Set
                              \<Rightarrow> ('\<AA>, _) Set)
                            \<Rightarrow> ('\<AA>, _) Set
                            \<Rightarrow> ('\<AA>, _) val set
                            \<Rightarrow> ('\<AA>, _) Set
                            \<Rightarrow> bool"
 for f and z  where
  EQ_emptyI [intro]: "EQ_fold_graph f z {} z" |
  EQ_insertI [intro]: "(\<lambda>_. x) \<notin> A \<Longrightarrow> \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow> EQ_fold_graph f z A y
      \<Longrightarrow> EQ_fold_graph f z (insert (\<lambda>_. x) A) (f (\<lambda>_. x) y)"

thm EQ_fold_graph_def
thm EQ_insertI
*)
(*
inductive_cases EQ_empty_fold_graphE [elim!]: "EQ_fold_graph f z {} x"
*)
*)

text{* We can now propose a locale generic enough
to represent both at the same time the previous @{term EQ_comp_fun_commute}
and the curried form of variables
(@{term f000} represents the parametrization): *}

locale EQ_comp_fun_commute0_gen0_bis'' =
  fixes f000 :: "'b \<Rightarrow> 'c"
  fixes is_i :: "'\<AA> st \<Rightarrow> 'c \<Rightarrow> bool"
  fixes is_i' :: "'\<AA> st \<Rightarrow> 'c \<Rightarrow> bool"
  fixes all_i_set :: "'c set \<Rightarrow> bool"

  fixes f :: "'c
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes i_set : "\<And>x A. all_i_set (insert x A) \<Longrightarrow> ((\<forall>\<tau>. is_i \<tau> x) \<and> all_i_set A)"
  assumes i_set' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (insert (f000 x) A)"
  assumes i_set'' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (A - {f000 x})"
  assumes i_set_finite : "\<And>A. all_i_set A \<Longrightarrow> finite A"
  assumes i_val : "\<And>x \<tau>. is_i \<tau> x \<Longrightarrow> is_i' \<tau> x"
  assumes f000_inj : "\<And>x y. x \<noteq> y \<Longrightarrow> f000 x \<noteq> f000 y"

  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (f000 x) S \<tau> = f (f000 x) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (f000 x) y)) = ((\<forall>\<tau>. is_i' \<tau> (f000 x)) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             (\<And>\<tau>. is_i' \<tau> (f000 x)) \<Longrightarrow>
                             (\<And>\<tau>. is_i' \<tau> (f000 y)) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (f000 y) (f (f000 x) S) = f (f000 x) (f (f000 y) S)"

text{* In the previous definition of the @{term EQ_comp_fun_commute} Isabelle locale,
it would be possible to write the associated Isabelle context
by following the contents of @{term comp_fun_commute},
and in particular there would be no need to change
the inductive definition of @{term fold_graph}.

However in order to perform inversion proofs transparently under @{term f000},
we replace now @{term fold_graph} by an other inductive definition
where @{term f000} appears as a protecting guard: *}

inductive EQG_fold_graph :: "('b \<Rightarrow> 'c)
                           \<Rightarrow> ('c
                             \<Rightarrow> ('\<AA>, 'a) Set
                             \<Rightarrow> ('\<AA>, 'a) Set)
                           \<Rightarrow> ('\<AA>, 'a) Set
                           \<Rightarrow> 'c set
                           \<Rightarrow> ('\<AA>, 'a) Set
                           \<Rightarrow> bool"
 for is_i and F and z where
 EQG_emptyI [intro]: "EQG_fold_graph is_i F z {} z" |
 EQG_insertI [intro]: "is_i x \<notin> A \<Longrightarrow>
                      EQG_fold_graph is_i F z A y \<Longrightarrow>
                      EQG_fold_graph is_i F z (insert (is_i x) A) (F (is_i x) y)"

inductive_cases EQG_empty_fold_graphE [elim!]: "EQG_fold_graph is_i f z {} x"
definition "foldG is_i f z A = (if finite A then (THE y. EQG_fold_graph is_i f z A y) else z)"

text{* Then the conversion from a @{term fold_graph} expression
 to a @{term EQG_fold_graph} expression always remembers its original image. *}

lemma eqg_fold_of_fold :
 assumes fold_g : "fold_graph F z (f000 ` A) y"
   shows "EQG_fold_graph f000 F z (f000 ` A) y"
  apply(insert fold_g)
  apply(subgoal_tac "\<And>A'. fold_graph F z A' y \<Longrightarrow> A' \<subseteq> f000 ` A \<Longrightarrow> EQG_fold_graph f000 F z A' y")
  apply(simp)
  proof - fix A' show "fold_graph F z A' y \<Longrightarrow> A' \<subseteq> f000 ` A \<Longrightarrow> EQG_fold_graph f000 F z A' y"
  apply(induction set: fold_graph)
  apply(rule EQG_emptyI)
  apply(simp, erule conjE)
  apply(drule imageE) prefer 2 apply assumption
  apply(simp)
  apply(rule EQG_insertI, simp, simp)
 done
qed

text{* In particular, the identity function is used when there is no choice. *}
lemma
 assumes fold_g : "fold_graph F z A y"
   shows "EQG_fold_graph (\<lambda>x. x) F z A y"
by (metis (mono_tags) eqg_fold_of_fold fold_g image_ident)

text{* Going from @{term EQG_fold_graph} to @{term fold_graph} provides the bijectivity. *}

lemma fold_of_eqg_fold :
 assumes fold_g : "EQG_fold_graph f000 F z A y"
   shows "fold_graph F z A y"
 apply(insert fold_g)
 apply(induction set: EQG_fold_graph)
 apply(rule emptyI)
 apply(simp add: insertI)
done

text{* Finally, the entire definition of the @{term EQ_comp_fun_commute0_gen0_bis''} context
could now depend uniquely on @{term EQG_fold_graph}. *}

context EQ_comp_fun_commute0_gen0_bis''
begin

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "\<forall>\<tau>. is_i' \<tau> (f000 a)"
   shows
   "EQG_fold_graph f000 f z A y \<Longrightarrow> (f000 a) \<in> A \<Longrightarrow> \<exists>y'. y = f (f000 a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQG_fold_graph f000 f z (A - {(f000 a)}) y'"
 apply(insert y_defined)
 proof (induct set: EQG_fold_graph)
   case (EQG_insertI x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f (f000 x) y)"
   then show "?case" when "\<forall>\<tau>. is_i' \<tau> (f000 x)" "(\<And>\<tau>. all_defined \<tau> y)"
   proof (insert that, cases "x = a") assume "x = a" with EQG_insertI show "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f (f000 a) y'" and "(\<forall>\<tau>. all_defined \<tau> y')" and y': "EQG_fold_graph f000 f z (A - {(f000 a)}) y'"
      using EQG_insertI by (metis insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "\<forall>\<tau>. is_i' \<tau> (f000 a) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply(simp only:)
       apply(subst (asm) cp_all_def) unfolding y apply(subst (asm) cp_all_def[symmetric])
       apply(insert all_def[where x = "a" and y = y', THEN iffD1], blast)
     done
     moreover have "\<forall>\<tau>. is_i' \<tau> (f000 x) \<Longrightarrow> \<forall>\<tau>. is_i' \<tau> (f000 a) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f (f000 x) y = f (f000 a) (f (f000 x) y')"
       unfolding y
     by(rule commute, blast+)
     moreover have "EQG_fold_graph f000 f z (insert (f000 x) A - {f000 a}) (f (f000 x) y')"
       using y' and `f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `f000 x \<notin> A`
       apply (simp add: insert_Diff_if Isabelle_Finite_Set.EQG_insertI)
     done
     apply_end(subgoal_tac "f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f (f000 x) y = f (f000 a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQG_fold_graph f000 f z (insert (f000 x) A - {(f000 a)}) y'")
     ultimately show "?case" when "(\<forall>\<tau>. is_i' \<tau> (f000 x)) \<and> f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y)" apply(auto simp: a_valid)
     by (metis (mono_tags) `\<And>\<tau>. all_defined \<tau> (f (f000 x) y)` all_def)
    apply_end(drule f000_inj, blast)+
   qed simp
  apply_end simp

  fix x y
  show "(\<And>\<tau>. all_defined \<tau> (f (f000 x) y)) \<Longrightarrow> \<forall>\<tau>. is_i' \<tau> (f000 x)"
   apply(rule all_def[where x = x and y = y, THEN iffD1, THEN conjunct1], simp) done

  fix x y \<tau>
  show "(\<And>\<tau>. all_defined \<tau> (f (f000 x) y)) \<Longrightarrow> all_defined \<tau> y"
   apply(rule all_def[where x = x, THEN iffD1, THEN conjunct2, THEN spec], simp) done

 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "\<forall>\<tau>. is_i' \<tau> (f000 x)"
       and "EQG_fold_graph f000 f z (insert (f000 x) A) v" and "(f000 x) \<notin> A"
   obtains y where "v = f (f000 x) y" and "is_i' \<tau> (f000 x)" and "\<And>\<tau>. all_defined \<tau> y" and "EQG_fold_graph f000 f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `EQG_fold_graph f000 f z (insert (f000 x) A) v` insertI1] x_valid `(f000 x) \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done

 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "EQG_fold_graph f000 f z A x \<Longrightarrow> EQG_fold_graph f000 f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: EQG_fold_graph)
   case (EQG_insertI x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f (f000 x) y)`
   have "\<forall>\<tau>. is_i' \<tau> (f000 x)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `\<forall>\<tau>. is_i' \<tau> (f000 x)` and `EQG_fold_graph f000 f z (insert (f000 x) A) v` and `(f000 x) \<notin> A`
   obtain y' where "v = f (f000 x) y'" and "\<And>\<tau>. all_defined \<tau> y'" and "EQG_fold_graph f000 f z A y'"
     by (rule fold_graph_insertE, simp)
   from EQG_insertI have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `EQG_fold_graph f000 f z A y'` have "y' = y" by (metis EQG_insertI.hyps(3))
   with `v = f (f000 x) y'` show "v = f (f000 x) y" by (simp)
   apply_end(rule_tac f = f in EQG_empty_fold_graphE, auto)
 qed

 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> z"
       and A_int : "all_i_set A"
     shows "EQG_fold_graph f000 f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: EQG_fold_graph)
   apply_end(simp)
   apply_end(subst all_def, drule i_set, auto, rule i_val, blast)
 qed

 lemma fold_graph_determ3 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_i_set A"
     shows "EQG_fold_graph f000 f z A x \<Longrightarrow> EQG_fold_graph f000 f z A y \<Longrightarrow> y = x"
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2[THEN spec]) apply(blast)+
  apply(rule det_init2[THEN spec]) apply(blast)+
 done

 lemma fold_graph_fold:
  assumes z_int : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
  shows "EQG_fold_graph f000 f z (f000 ` A) (foldG f000 f z (f000 ` A))"
 proof -
  from A_int have "finite (f000 ` A)" by (simp add: i_set_finite)
  then have "\<exists>x. fold_graph f z (f000 ` A) x" by (rule finite_imp_fold_graph)
  then have "\<exists>x. EQG_fold_graph f000 f z (f000 ` A) x" by (metis eqg_fold_of_fold)
  moreover note fold_graph_determ3[OF z_int A_int]
  ultimately have "\<exists>!x. EQG_fold_graph f000 f z (f000 ` A) x" by(rule ex_ex1I)
  then have "EQG_fold_graph f000 f z (f000 ` A) (The (EQG_fold_graph f000 f z (f000 ` A)))" by (rule theI')
  then show ?thesis by(simp add: `finite (f000 \` A)` foldG_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
     shows "EQG_fold_graph f000 f z (f000 ` A) y \<Longrightarrow> foldG f000 f z (f000 ` A) = y"
  apply(rule fold_graph_determ3[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done

 lemma fold_insert:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_i_set (f000 ` A)"
       and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
       and x_nA : "f000 x \<notin> f000 ` A"
   shows "foldG f000 f z (f000 ` (insert x A)) = f (f000 x) (foldG f000 f z (f000 ` A))"
 proof (rule fold_equality)
   have "EQG_fold_graph f000 f z (f000 `A) (foldG f000 f z (f000 `A))" by (rule fold_graph_fold[OF z_defined A_int])
   with x_nA show "EQG_fold_graph f000 f z (f000 `(insert x A)) (f (f000 x) (foldG f000 f z (f000 `A)))" apply(simp add: image_insert) by(rule EQG_insertI, simp, simp)
   apply_end (simp add: z_defined)
   apply_end (simp only: image_insert)
   apply_end(rule i_set', simp add: x_int A_int)
 qed

 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
      and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` A))"
  proof -
   have eq_f : "\<And>A. Finite_Set.fold f z (f000 ` A) = foldG f000 f z (f000 ` A)"
    apply(simp add: Finite_Set.fold_def foldG_def)
   by (rule impI, metis eqg_fold_of_fold fold_of_eqg_fold)

  have x_nA : "f000 x \<notin> f000 ` A"
   apply(simp add: image_iff)
  by (metis x_nA f000_inj)

  have "foldG f000 f z (f000 ` insert x A) = f (f000 x) (foldG f000 f z (f000 ` A))"
   apply(rule fold_insert) apply(simp add: assms x_nA)+
  done

  thus ?thesis by (subst (1 2) eq_f, simp)
 qed

 lemma all_int_induct :
   assumes i_fin : "all_i_set (f000 ` F)"
   assumes "P {}"
       and insert: "\<And>x F. all_i_set (f000 ` F) \<Longrightarrow> \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> x \<notin> F \<Longrightarrow> P (f000 ` F) \<Longrightarrow> P (f000 ` (insert x F))"
   shows "P (f000 ` F)"
 proof -
  from i_fin have "finite (f000 ` F)" by (simp add: i_set_finite)
  then have "finite F" apply(rule finite_imageD) apply(simp add: inj_on_def, insert f000_inj, blast) done
  show "?thesis"
  using `finite F` and i_fin
  proof induct
    apply_end(simp)
    show "P {}" by fact
    apply_end(simp add: i_set)
    apply_end(rule insert[simplified], simp add: i_set, simp add: i_set)
    apply_end(simp, simp)
  qed
 qed

 lemma all_defined_fold_rec :
  assumes A_defined : "\<And>\<tau>. all_defined \<tau> A"
      and x_notin : "x \<notin> Fa"
    shows "
        all_i_set (f000 ` insert x Fa) \<Longrightarrow>
        (\<And>\<tau>. all_defined \<tau> (Finite_Set.fold f A (f000 ` Fa))) \<Longrightarrow>
        all_defined \<tau> (Finite_Set.fold f A (f000 ` insert x Fa))"
  apply(subst (asm) image_insert)
  apply(frule i_set[THEN conjunct1])
  apply(subst fold_insert'[OF A_defined])
   apply(rule i_set[THEN conjunct2], simp)
   apply(simp)
   apply(simp add: x_notin)
  apply(rule all_def[THEN iffD2, THEN spec])
  apply(simp add: i_val)
 done

 lemma fold_def :
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes F_int : "all_i_set (f000 ` F)"
   shows "all_defined \<tau> (Finite_Set.fold f z (f000 ` F))"
 apply(subgoal_tac "\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold f z (f000 ` F))", blast)
 proof (induct rule: all_int_induct[OF F_int])
  apply_end(simp add:z_def)
  apply_end(rule allI)
  apply_end(rule all_defined_fold_rec[OF z_def], simp, simp add: i_set', blast)
 qed

 lemma fold_fun_comm:
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes A_int : "all_i_set (f000 ` A)"
       and x_val : "\<And>\<tau>. is_i' \<tau> (f000 x)"
     shows "f (f000 x) (Finite_Set.fold f z (f000 ` A)) = Finite_Set.fold f (f (f000 x) z) (f000 ` A)"
 proof -
  have fxz_def: "\<And>\<tau>. all_defined \<tau> (f (f000 x) z)"
  by(rule all_def[THEN iffD2, THEN spec], simp add: z_def x_val)

  show ?thesis
  proof (induct rule: all_int_induct[OF A_int])
   apply_end(simp)
   apply_end(rename_tac x' F)
   apply_end(subst fold_insert'[OF z_def], simp, simp, simp)
   apply_end(subst fold_insert'[OF fxz_def], simp, simp, simp)
   apply_end(subst commute[symmetric])
   apply_end(simp add: x_val)
   apply_end(rule i_val, blast)
   apply_end(subst fold_def[OF z_def], simp_all)
  qed
 qed

 lemma fold_rec:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_i_set (f000 ` A)"
        and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
        and "x \<in> A"
   shows "Finite_Set.fold f z (f000 ` A) = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))"
 proof -
   have f_inj : "inj f000" by (simp add: inj_on_def, insert f000_inj, blast)
   from A_int have A_int: "all_i_set (f000 ` (A - {x}))" apply(subst image_set_diff[OF f_inj]) apply(simp, rule i_set'', simp add: x_int) done
   have A: "f000 ` A = insert (f000 x) (f000 ` (A - {x}))" using `x \<in> A` by blast
   then have "Finite_Set.fold f z (f000 ` A) = Finite_Set.fold f z (insert (f000 x) (f000 ` (A - {x})))" by simp
   also have "\<dots> = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))" by(simp only: image_insert[symmetric], rule fold_insert'[OF z_defined A_int x_int], simp)
   finally show ?thesis .
 qed

 lemma fold_insert_remove:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_i_set (f000 ` A)"
        and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
   shows "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))"
 proof -
   from A_int have "finite (f000 ` A)" by (simp add: i_set_finite)
   then have "finite (f000 ` insert x A)" by auto
   moreover have "x \<in> insert x A" by auto
   moreover from A_int have A_int: "all_i_set (f000 ` insert x A)" by (simp, subst i_set', simp_all add: x_int)
   ultimately have "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` (insert x A - {x})))"
   by (subst fold_rec[OF z_defined A_int x_int], simp_all)
   then show ?thesis by simp
 qed

 lemma finite_fold_insert :
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
      and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
      and "x \<notin> A"
   shows "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Finite_Set.fold f z (f000 ` insert x A) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f (f000 x) (Finite_Set.fold f z (f000 ` A)) \<tau>)\<rceil>\<rceil>"
   apply(subst fold_insert', simp_all add: assms)
 done

 lemma (*c_fun_commute:*)
  assumes s_not_def : "\<And>x S. \<not> (\<forall>\<tau>. (\<tau> \<Turnstile> \<delta> S))             \<Longrightarrow> f x S = \<bottom>"
  assumes s_not_fin : "\<And>x S \<tau>. \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> f x S = \<bottom>"
  assumes x_not_i   : "\<And>x S. \<not> (\<forall>\<tau>. is_i' \<tau> x)             \<Longrightarrow> f x S = \<bottom>"
  assumes s_bot : "\<And>x. f x \<bottom> = \<bottom>"
  shows "comp_fun_commute (f o f000)"
 proof -
  have s_not_fin : "\<And>x S. \<not> (\<forall>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow> f x S = \<bottom>" by (metis s_not_fin)
  show ?thesis
   apply(standard, simp add: comp_def)
   apply(rule ext, rename_tac S)
   apply(rule ext, rename_tac \<tau>)
   apply(case_tac "\<not> (\<forall>\<tau>. (\<tau> \<Turnstile> \<delta> S))", simp add: s_not_def s_bot)
   apply(case_tac "\<not> (\<forall>\<tau>. all_defined \<tau> S)", simp add: all_defined_def all_defined_set'_def s_not_fin s_bot)
   apply(case_tac "\<not> (\<forall>\<tau>. is_i' \<tau> (f000 x))", simp add: x_not_i s_bot)
   apply(case_tac "\<not> (\<forall>\<tau>. is_i' \<tau> (f000 y))", simp add: x_not_i s_bot)
  by(subst commute, blast+)
 qed
end

lemma (*comp_to_EQ_comp_fun_commute0_gen0_bis'' :*)
 assumes f_comm: "comp_fun_commute f"

 assumes i_set : "\<And>x A. all_i_set (insert x A) \<Longrightarrow> ((\<forall>\<tau>. is_i \<tau> x) \<and> all_i_set A)"
 assumes i_set' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (insert (f000 x) A)"
 assumes i_set'' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (A - {f000 x})"
 assumes i_set_finite : "\<And>A. all_i_set A \<Longrightarrow> finite A"
 assumes i_val : "\<And>x \<tau>. is_i \<tau> x \<Longrightarrow> is_i' \<tau> x"
 assumes f000_inj : "\<And>x y. x \<noteq> y \<Longrightarrow> f000 x \<noteq> f000 y"
 assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (f000 x) S \<tau> = f (f000 x) (\<lambda>_. S \<tau>) \<tau>"
 assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (f000 x) y)) = ((\<forall>\<tau>. is_i' \<tau> (f000 x)) \<and> (\<forall>\<tau>. all_defined \<tau> y))"

 shows "EQ_comp_fun_commute0_gen0_bis'' f000 is_i is_i' all_i_set f"
proof - interpret comp_fun_commute f by (rule f_comm) show ?thesis
  apply(standard)
  apply(rule i_set, blast+)
  apply(rule i_set', blast+)
  apply(rule i_set'', blast+)
  apply(rule i_set_finite, blast+)
  apply(rule i_val, blast+)
  apply(rule f000_inj, blast+)
  apply(rule cp_set, blast+)
  apply(rule all_def)
  apply(rule fun_left_comm)
 done
qed

locale EQ_comp_fun_commute0_gen0_bis' = EQ_comp_fun_commute0_gen0_bis'' +
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f (f000 x) S \<tau>1 = f (f000 x) S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f (f000 x) S \<tau>)\<rceil>\<rceil> \<noteq> {}"

context EQ_comp_fun_commute0_gen0_bis'
begin
 lemma downgrade_up : "EQ_comp_fun_commute0_gen0_bis'' f000 is_i is_i' all_i_set f" by standard
 lemma downgrade : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f" by standard
end

 lemma fold_cong''' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and t_def : "\<And>\<tau>. all_defined \<tau> t"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s \<tau> = t \<tau>'"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>'"
 proof -
  interpret EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f by (rule f_comm)
  note g_comm_down = g_comm[THEN EQ_comp_fun_commute0_gen0_bis'.downgrade_up]
  note g_fold_insert' = EQ_comp_fun_commute0_gen0_bis''.fold_insert'[OF g_comm_down]
  note g_cp_set = EQ_comp_fun_commute0_gen0_bis''.cp_set[OF g_comm_down]
  note g_fold_def = EQ_comp_fun_commute0_gen0_bis''.fold_def[OF g_comm_down]
  note g_cp_gen = EQ_comp_fun_commute0_gen0_bis'.cp_gen[OF g_comm]
  have "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` A) \<tau>'"
   apply(rule all_int_induct[OF a_def], simp add: st)
   apply(subst fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_fold_insert', simp add: t_def, simp, simp, simp)
   apply(subst g_cp_set, rule allI, rule g_fold_def, simp add: t_def, simp)
   apply(drule sym, simp)
   apply(subst g_cp_gen[of _ _ _ \<tau>], simp, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp, simp)
   apply(subst g_cp_set[symmetric], rule allI, rule fold_def, simp add: s_def, simp)
   apply(rule cong, simp)
   (* *)
   apply(rule all_int_induct, simp, simp add: P0, simp add: st[symmetric] P0)
   apply(rule Prec[simplified], simp_all)
  done
  thus ?thesis by (simp add: st[symmetric] ab[symmetric])
 qed

 lemma fold_cong'' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s = t"
      and stau : "s \<tau> = s \<tau>'"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>'"
 proof -
  interpret EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f by (rule f_comm)
  note g_comm_down = g_comm[THEN EQ_comp_fun_commute0_gen0_bis'.downgrade_up]
  note g_fold_insert' = EQ_comp_fun_commute0_gen0_bis''.fold_insert'[OF g_comm_down]
  note g_cp_set = EQ_comp_fun_commute0_gen0_bis''.cp_set[OF g_comm_down]
  note g_fold_def = EQ_comp_fun_commute0_gen0_bis''.fold_def[OF g_comm_down]
  note g_cp_gen = EQ_comp_fun_commute0_gen0_bis'.cp_gen[OF g_comm]
  have "Finite_Set.fold g s (f000 ` A) \<tau>' = Finite_Set.fold f s (f000 ` A) \<tau>"
   apply(rule all_int_induct[OF a_def], simp add: stau)
   apply(subst fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_cp_set, rule allI, rule g_fold_def, simp add: s_def, simp)
   apply(simp, subst g_cp_set[symmetric], rule allI, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp)
   apply(subst g_cp_gen[of _ _ _ \<tau>], simp, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp, simp)
   apply(subst g_cp_set[symmetric], rule allI, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp)
   apply(rule cong[symmetric], simp)
   (* *)
   apply(rule all_int_induct, simp, simp add: P0, simp add: st[symmetric] P0)
   apply(rule Prec[simplified], simp_all)
  done
  thus ?thesis by (simp add: st[symmetric] ab[symmetric])
 qed

 lemma fold_cong' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s = t"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>"
 by(rule fold_cong''[OF f_comm g_comm a_def s_def cong ab st], simp, simp, simp, rule P0, rule Prec, blast+)

 lemma fold_cong :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<Longrightarrow> f (f000 x) s = g (f000 x) s)"
      and ab : "A = B"
      and st : "s = t"
      and P0 : "P s"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F))"
    shows "Finite_Set.fold f s (f000 ` A) = Finite_Set.fold g t (f000 ` B)"
  apply(rule ext, rule fold_cong'[OF f_comm g_comm a_def s_def])
  apply(subst cong, simp, simp, simp, rule ab, rule st, rule P0)
  apply(rule Prec, simp_all)
 done


subsection{* Sublocale *}

locale EQ_comp_fun_commute =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_x : "\<And>x S \<tau>. f x S \<tau> = f (\<lambda>_. x \<tau>) S \<tau>"
  assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. is_int x \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y \<tau>. all_defined \<tau> (f x y) = (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"
  assumes commute: "\<And>x y S \<tau>.
                             \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             all_defined \<tau> S \<Longrightarrow>
                             f y (f x S) \<tau> = f x (f y S) \<tau>"

lemma (*comp_to_EQ_comp_fun_commute :*)
 assumes f_comm: "comp_fun_commute f"

 assumes cp_x : "\<And>x S \<tau>. f x S \<tau> = f (\<lambda>_. x \<tau>) S \<tau>"
 assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
 assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. is_int x \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
 assumes notempty : "\<And>x S \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
 assumes all_def: "\<And>x y \<tau>. all_defined \<tau> (f x y) = (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"

 shows "EQ_comp_fun_commute f"
 proof - interpret comp_fun_commute f by (rule f_comm) show ?thesis
  apply(standard)
  apply(rule cp_x)
  apply(rule cp_set)
  apply(rule cp_gen, assumption+)
  apply(rule notempty, blast+)
  apply(rule all_def)
 by(subst fun_left_comm, simp)
qed

sublocale EQ_comp_fun_commute < EQ_comp_fun_commute0_gen0_bis' "\<lambda>x. x" "\<lambda>_. is_int" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" all_int_set
 apply(standard)
 apply(simp add: all_int_set_def) apply(simp add: all_int_set_def) apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: int_is_valid, simp)
 apply(rule cp_set)
 apply(rule iffI)
 apply(rule conjI) apply(rule allI) apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption apply(rule all_def[THEN iffD1, THEN conjunct1], blast)
 apply(rule allI) apply(drule allE) prefer 2 apply assumption apply(rule all_def[THEN iffD1, THEN conjunct2], blast)
 apply(erule conjE) apply(rule allI)  apply(rule all_def[THEN iffD2], blast)
 apply(rule ext, rename_tac \<tau>)
 apply(rule commute) apply(blast)+
 apply(rule cp_gen, simp, blast, simp)
 apply(rule notempty, blast, simp add: int_is_valid, simp)
done

locale EQ_comp_fun_commute0_gen0 =
  fixes f000 :: "'b \<Rightarrow> ('\<AA>, 'a option option) val"
  fixes all_def_set :: "'\<AA> st \<Rightarrow> 'b set \<Rightarrow> bool"
  fixes f :: "'b
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes def_set : "\<And>x A. (\<forall>\<tau>. all_def_set \<tau> (insert x A)) = (is_int (f000 x) \<and> (\<forall>\<tau>. all_def_set \<tau> A))"
  assumes def_set' : "\<And>x A. (is_int (f000 x) \<and> (\<forall>\<tau>. all_def_set \<tau> A)) \<Longrightarrow> \<forall>\<tau>. all_def_set \<tau> (A - {x})"
  assumes def_set_finite : "\<forall>\<tau>. all_def_set \<tau> A \<Longrightarrow> finite A"
  assumes all_i_set_to_def : "all_int_set (f000 ` F) \<Longrightarrow> \<forall>\<tau>. all_def_set \<tau> F"

  assumes f000_inj : "\<And>x y. x \<noteq> y \<Longrightarrow> f000 x \<noteq> f000 y"

  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (f000 x) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"

  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (f000 x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (f000 x) \<Longrightarrow>
                             is_int (f000 y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0_gen0 < EQ_comp_fun_commute0_gen0_bis' "\<lambda>x. x" "\<lambda>_ x. is_int (f000 x)" "\<lambda>_ x. is_int (f000 x)" "\<lambda>x. \<forall>\<tau>. all_def_set \<tau> x"
 apply standard
 apply(drule def_set[THEN iffD1], blast)
 apply(simp add: def_set[THEN iffD2])
 apply(simp add: def_set')
 apply(simp add: def_set_finite)
 apply(simp)
 apply(simp)
 apply(rule cp_set, simp)
 apply(insert all_def, blast)
 apply(rule commute, blast+)
 apply(rule cp_gen', blast+)
 apply(rule notempty', blast+)
done

locale EQ_comp_fun_commute0 =
  fixes f :: "'a option option
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0 < EQ_comp_fun_commute0_gen0 "\<lambda>x (_::'\<AA> st). x" all_defined_set
 apply standard
 apply(rule iffI)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def)
 apply(simp add: all_int_set_def all_defined_set_def int_is_valid)
 apply(rule finite_imageD, blast, metis inj_onI)
 apply metis
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute, simp, simp, blast)
done

locale EQ_comp_fun_commute000 =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (\<lambda>(_::'\<AA> st). x) S \<tau> = f (\<lambda>(_::'\<AA> st). x) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (\<lambda>(_::'\<AA> st). x) y)) = (is_int (\<lambda>(_ :: '\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>(_::'\<AA> st). y) (f (\<lambda>(_::'\<AA> st). x) S) = f (\<lambda>(_::'\<AA> st). x) (f (\<lambda>(_::'\<AA> st). y) S)"

sublocale EQ_comp_fun_commute000 < EQ_comp_fun_commute0_gen0_bis'' "\<lambda>x (_::'\<AA> st). x" "\<lambda>_. is_int" "\<lambda>_. is_int" all_int_set
 apply standard
  apply(simp add: all_int_set_def is_int_def)
  apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: all_int_set_def)
 apply(simp)
 apply(metis)
 apply(rule cp_set, simp)
 apply(insert all_def, blast)
 apply(rule commute, simp, simp, blast)
done

lemma c0_of_c :
 assumes f_comm : "EQ_comp_fun_commute f"
   shows "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
proof - interpret EQ_comp_fun_commute f by (rule f_comm) show ?thesis
 apply standard
 apply(rule cp_set)
 apply(subst cp_gen, simp, blast, simp, simp)
 apply(rule notempty, blast, simp add: int_is_valid, simp)
 apply (metis (mono_tags) all_def is_int_def)

 apply(rule ext, rename_tac \<tau>)
 apply(subst commute)
 apply (metis is_int_def)+
 done
qed

lemma c000_of_c0 :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute000 f"
proof - interpret EQ_comp_fun_commute0 "\<lambda>x. f (\<lambda>_. x)" by (rule f_comm) show ?thesis
 apply standard
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute)
 apply(blast)+
 done
qed

locale EQ_comp_fun_commute0' =
  fixes f :: "'a option
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0' < EQ_comp_fun_commute0_gen0 "\<lambda>x (_::'\<AA> st). \<lfloor>x\<rfloor>" all_defined_set'
 apply standard
 apply(rule iffI)
  apply(simp add: all_defined_set'_def is_int_def, metis bot_option_def foundation18' option.distinct(1))
  apply(simp add: all_defined_set'_def is_int_def)
 apply(simp add: all_defined_set'_def is_int_def)
  apply(simp add: all_defined_set'_def)
 apply(simp add: all_int_set_def all_defined_set'_def int_is_valid)
 apply(rule finite_imageD, blast, metis (full_types) UNIV_I inj_Some inj_fun subsetI subset_inj_on)
 apply (metis option.inject)
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute, simp, simp, blast)
done

locale EQ_comp_fun_commute000' =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (\<lambda>_. \<lfloor>x\<rfloor>) S \<tau> = f (\<lambda>_. \<lfloor>x\<rfloor>) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y (\<tau> :: '\<AA> st). (\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> (f (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) y)) = (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> y))"
  assumes commute: "\<And>x y S (\<tau> :: '\<AA> st).
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>x\<rfloor>) \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>_. \<lfloor>y\<rfloor>) (f (\<lambda>_. \<lfloor>x\<rfloor>) S) = f (\<lambda>_. \<lfloor>x\<rfloor>) (f (\<lambda>_. \<lfloor>y\<rfloor>) S)"

sublocale EQ_comp_fun_commute000' < EQ_comp_fun_commute0_gen0_bis'' "\<lambda>x (_::'\<AA> st). \<lfloor>x\<rfloor>" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" all_int_set
 apply standard
 apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: all_int_set_def)
 apply(simp)
 apply (metis option.inject)
 apply(rule cp_set, simp)
 apply(rule iffI)
 apply(rule conjI, rule allI)
 apply(rule all_def[THEN iffD1, THEN conjunct1], blast)
 apply(rule all_def[THEN iffD1, THEN conjunct2], blast)
 apply(rule all_def[THEN iffD2], blast)
 apply(rule commute, blast+)
done

lemma c0'_of_c0 :
 assumes "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. f (\<lambda>_. x)" by (rule assms) show ?thesis
 apply standard
 apply(rule cp_set, simp)
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule all_def)
 apply(rule commute) apply(blast)+
 done
qed

lemma c000'_of_c0' :
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "EQ_comp_fun_commute000' f"
proof - interpret EQ_comp_fun_commute0' "\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm) show ?thesis
 apply standard
 apply(rule cp_set, simp)
 apply(subst all_def, simp only: is_int_def valid_def OclValid_def bot_fun_def false_def true_def, blast)
 apply(rule commute)
 apply(simp add: int_trivial)+
 done
qed

context EQ_comp_fun_commute
begin
 lemmas F_cp = cp_x
 lemmas F_cp_set = cp_set
 lemmas fold_fun_comm = fold_fun_comm[simplified]
 lemmas fold_insert_remove = fold_insert_remove[simplified]
 lemmas fold_insert = fold_insert'[simplified]
 lemmas all_int_induct = all_int_induct[simplified]
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
 lemmas downgrade = downgrade
end

context EQ_comp_fun_commute000
begin
 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: '\<AA> st). a) ` A)"
      and x_int : "is_int (\<lambda>(_ :: '\<AA> st). x)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). a) ` (insert x A)) = f (\<lambda>(_ :: '\<AA> st). x) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). a) ` A))"
  apply(rule fold_insert', simp_all add: assms)
 done

 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified]
 lemmas fold_def = fold_def
end

context EQ_comp_fun_commute000'
begin
 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` A)"
      and x_int : "is_int (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` (insert x A)) = f (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` A))"
  apply(rule fold_insert', simp_all only: assms)
  apply(insert x_int[simplified is_int_def], auto)
 done

 lemmas fold_def = fold_def
end

context EQ_comp_fun_commute0_gen0
begin
 lemma fold_insert:
   assumes z_defined : "\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: '\<AA> st). all_def_set \<tau> A"
       and x_int : "is_int (f000 x)"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
 by(rule fold_insert'[simplified], simp_all add: assms)

 lemmas downgrade = downgrade
end

context EQ_comp_fun_commute0
begin
 lemmas fold_insert = fold_insert
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
end

context EQ_comp_fun_commute0'
begin
 lemmas fold_insert = fold_insert
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
end

subsection{* Misc *}

lemma img_fold :
 assumes g_comm : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. G (f000 x))"
     and a_def : "\<forall>\<tau>. all_defined \<tau> A"
     and fini : "all_int_set (f000 ` Fa)"
     and g_fold_insert : "\<And>x F. x \<notin> F \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` F) \<Longrightarrow> Finite_Set.fold G A (insert (f000 x) (f000 ` F)) = G (f000 x) (Finite_Set.fold G A (f000 ` F))"
   shows  "Finite_Set.fold (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) A (f000 ` Fa) =
           Finite_Set.fold (\<lambda>x. G (f000 x)) A Fa"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. G (f000 x)" by (rule g_comm)
 show ?thesis
  apply(rule finite_induct[where P = "\<lambda>set. let set' = f000 ` set in
                                               all_int_set set' \<longrightarrow>
                                               Finite_Set.fold G A set' = Finite_Set.fold (\<lambda>x. G (f000 x)) A set"
                  and F = Fa, simplified Let_def, THEN mp])
  apply(insert fini[simplified all_int_set_def, THEN conjunct1], rule finite_imageD, assumption)
  apply (metis f000_inj inj_onI)
  apply(simp)
  apply(rule impI)+

  apply(subgoal_tac "all_int_set (f000 ` F)", simp)

  apply(subst EQ_comp_fun_commute0_gen0.fold_insert[OF g_comm])
   apply(simp add: a_def)
   apply(simp add: all_i_set_to_def)
   apply(simp add: invert_int)
   apply(simp)
   apply(drule sym, simp only:)
   apply(subst g_fold_insert, simp, simp add: invert_int, simp)
  apply(simp)

  apply(rule invert_all_int_set, simp)
  apply(simp add: fini)
 done
qed

context EQ_comp_fun_commute0_gen0 begin lemma downgrade' : "EQ_comp_fun_commute0_gen0 f000 all_def_set f" by standard end
context EQ_comp_fun_commute0 begin lemmas downgrade' = downgrade' end
context EQ_comp_fun_commute0' begin lemmas downgrade' = downgrade' end

end
