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

chapter\<open>Part ...\<close>

theory Aux_proof
imports Main
begin

section\<open>On the Semantics of Object-oriented Data Structures and Path Expressions\<close>

subsection\<open>Basic modelization of attributes\<close>

datatype oid = Oid
datatype attr_own = Attr_own
datatype attr_inh = Attr_inh
datatype '\<alpha> recurse = R nat '\<alpha>

subsection\<open>Datatype definition of the class type and class type extension (version 1)\<close>

datatype t1_ext = T1_ext attr_own "(t1_ext recurse) option"
datatype t1 = T1 oid attr_own attr_inh "(t1_ext recurse) option"

subsection\<open>Datatype definition of the class type and class type extension (version 2)\<close>

datatype t2_ext = T2_ext_oid oid attr_inh
                | T2_ext_rec "t2 recurse"
     and t2 = T2 t2_ext attr_own

fun get2_oid where
   "get2_oid v = (\<lambda> T2 (T2_ext_oid oid _) _ \<Rightarrow> oid
                  | T2 (T2_ext_rec (R _ t)) _ \<Rightarrow> get2_oid t) v"

fun get2_inh where
   "get2_inh v = (\<lambda> T2 (T2_ext_oid _ inh) _ \<Rightarrow> inh
                  | T2 (T2_ext_rec (R _ t)) _ \<Rightarrow> get2_inh t) v"

subsection\<open>Datatype definition of the class type and class type extension (version 3)\<close>

datatype t3_ext = T3_ext_oid oid attr_inh attr_own
                | T3_ext_rec "t3 recurse"
     and t3 = T3 t3_ext

fun get3_oid where
   "get3_oid v = (\<lambda> T3 (T3_ext_oid oid _ _) \<Rightarrow> oid
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_oid t) v"

fun get3_inh where
   "get3_inh v = (\<lambda> T3 (T3_ext_oid _ inh _) \<Rightarrow> inh
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_inh t) v"

fun get3_own where
   "get3_own v = (\<lambda> T3 (T3_ext_oid _ _ own) \<Rightarrow> own
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_own t) v"

subsection\<open>Conversion t2 of t1\<close>

fun m2_of_m1_ext where
   "m2_of_m1_ext oid attr_inh m1 = (\<lambda> T1_ext attr_own opt \<Rightarrow> T2 (case opt
      of None \<Rightarrow> T2_ext_oid oid attr_inh
       | Some (R ide m1) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid attr_inh m1))) attr_own) m1"

definition "m2_of_m1 = (\<lambda> T1 oid attr_own attr_inh opt \<Rightarrow> T2 (case opt
   of None \<Rightarrow> T2_ext_oid oid attr_inh
    | Some (R ide m1) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid attr_inh m1))) attr_own)"

subsection\<open>Conversion t1 of t2\<close>

fun m1_ext_of_m2 where
   "m1_ext_of_m2 m2 =
  (\<lambda> T2 (T2_ext_oid _ _) attr_own \<Rightarrow> T1_ext attr_own None
   | T2 (T2_ext_rec (R ide m2)) attr_own \<Rightarrow> T1_ext attr_own (Some (R ide (m1_ext_of_m2 m2)))) m2"

definition "m1_of_m2 =
  (\<lambda> T2 (T2_ext_oid oid attr_inh) attr_own \<Rightarrow> T1 oid attr_own attr_inh None
   | T2 (T2_ext_rec (R ide m2)) attr_own \<Rightarrow> T1 (get2_oid m2) attr_own (get2_inh m2) (Some (R ide (m1_ext_of_m2 m2))))"

subsection\<open>Bijectivity proofs\<close>

lemma "m1_of_m2 (m2_of_m1 X) = X"
 apply(case_tac X, simp)
 subgoal for oid attr_own attr_inh option
  apply(case_tac option, simp add: m1_of_m2_def m2_of_m1_def, simp)
  subgoal for a
   apply(case_tac a)
   apply(rule t1_ext.induct[where P = "\<lambda>x2. \<forall>a x1. a = R x1 x2 \<longrightarrow>
     m1_of_m2 (m2_of_m1 (T1 oid attr_own attr_inh (Some a))) = T1 oid attr_own attr_inh (Some a)",
                            THEN spec, THEN spec, THEN mp])
   apply(intro allI impI)
   subgoal for _ _ _ x2a
    apply(case_tac x2a, simp add: m1_of_m2_def m2_of_m1_def, simp)
    subgoal for aa
    by(case_tac aa, simp add: m1_of_m2_def m2_of_m1_def)
   done
  by simp
 done
done

lemma t2_ext_t2_induct :
 assumes H1 [simp]: "(\<And>oid attr_inh. P1 (T2_ext_oid oid attr_inh))"
 assumes H2 [simp]: "(\<And>recurse. P3 recurse \<Longrightarrow> P1 (T2_ext_rec recurse))"
 assumes H3 [simp]: "(\<And>t2_ext attr_own. P1 t2_ext \<Longrightarrow> P2 (T2 t2_ext attr_own))"
 assumes H4 [simp]: "(\<And>nat t2. P2 t2 \<Longrightarrow> P3 (R nat t2))"
 shows "P1 t2_ext \<and> P2 t2_0 \<and> P3 recurse"
proof -
 have X1: "\<And>t2_ext. P1 t2_ext"
  apply(rule t2_ext.induct[of _ "\<lambda>xa. \<forall>n. P3 (R n xa)"], simp)
  subgoal for _ x
  by(case_tac x, simp)
 by auto

 have X2: "\<And>t2_0. P2 t2_0"
  apply(rule t2.induct[of "\<lambda>t2_ext. P1 t2_ext \<and> (case t2_ext of T2_ext_rec (R n xa) \<Rightarrow> P3 (R n xa)
                                                              | _ \<Rightarrow> True)"],
        simp, simp)
  subgoal for x
  by(case_tac x, simp)
 by simp

 show ?thesis
  apply(intro conjI)
  apply(rule X1)
  apply(rule X2)

  apply(case_tac recurse, simp)
  subgoal for _ x2
   apply(subgoal_tac "P2 x2", simp)
  by(rule X2)
 done
qed

lemma "m2_of_m1 (m1_of_m2 X) = X"
 apply(case_tac X, simp)
 proof -
  fix t2_ext attr_own
  define P where "P \<equiv> \<lambda>X. m2_of_m1 (m1_of_m2 X) = X"
  show "m2_of_m1 (m1_of_m2 (T2 t2_ext attr_own)) = T2 t2_ext attr_own"
   apply(rule t2_ext_t2_induct[ of "\<lambda>t2_ext. \<forall>attr_own. P (T2 t2_ext attr_own)"
                                   "\<lambda>recurse. \<forall>attr_own. P (T2 (T2_ext_rec recurse) attr_own)"
                                   "\<lambda>option. \<forall>nat attr_own. P (T2 (T2_ext_rec (R nat option)) attr_own)"
                              , THEN conjunct1, THEN spec, simplified Let_def P_def])
   apply(auto)
   apply(subst m1_of_m2_def, subst m2_of_m1_def, auto)+

   subgoal for t2_ext x
    apply(subgoal_tac "(
     let oid = case t2_ext of T2_ext_oid oid _ \<Rightarrow> oid | T2_ext_rec (R _ xb) \<Rightarrow> get2_oid xb
       ; inh = case t2_ext of T2_ext_oid _ inh \<Rightarrow> inh | T2_ext_rec (R _ xb) \<Rightarrow> get2_inh xb in

     T2 (case t2_ext of T2_ext_oid _ _ \<Rightarrow> T2_ext_oid oid inh | T2_ext_rec (R ide m2) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid inh (m1_ext_of_m2 m2))) ) x) =
            T2 t2_ext x")
    apply(simp add: Let_def) apply(case_tac t2_ext, simp, simp) subgoal for x2 by(case_tac x2, simp)

    apply(case_tac t2_ext, simp, simp)
    apply(subst (asm) m2_of_m1_def, subst (asm) m1_of_m2_def, simp)
    proof -
    define P where "P \<equiv> \<lambda>recurse. (case recurse of R ide m2 \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext (case recurse of R xa x \<Rightarrow> get2_oid x) (case recurse of R xa x \<Rightarrow> get2_inh x) (m1_ext_of_m2 m2)))) =
                                  T2_ext_rec recurse"
    fix recurse
    show "P recurse"
     apply(rule t2_ext_t2_induct[ of "\<lambda>t2_ext. \<forall>nat attr_own. P (R nat (T2 t2_ext attr_own))"
                                     "\<lambda>recurse. P recurse"
                                     "\<lambda>t2. \<forall>nat attr_own. P (R nat t2)"
                                , THEN conjunct2, THEN conjunct2], simp_all add: P_def)
     subgoal for recurse
     by(case_tac recurse, simp)
    done
   qed
  done
qed

end
