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

chapter{* Part ... *}

theory   Bank_Test_Model
imports
  "../src/UML_OCL"
begin

Class Account
Attributes account_id : Integer
           balance    : Integer

Context c: Account
  Inv "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t (c .balance)"


Class Client
Attributes client_id : Integer
           name      : String

Association owner
  Between Account [1 \<bullet>\<bullet> *] Role accounts
          Client  [1]      Role owner

Association manages
  Between Account [1 \<bullet>\<bullet> *] Role managed_accounts
          Bank [1]         Role bank

Class Bank
Attributes bank_name : String

End! (* Bang forces generation of the oo - datatype theory *)

Context Bank :: deposit (c : Client, account_id : Integer, amount:Integer)
  Pre  "def": "(\<delta> c) and (\<delta> account_id) and (\<delta> amount)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  "pos": "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A  = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                            ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance +\<^sub>i\<^sub>n\<^sub>t  amount)"

Context Bank :: withdraw (c : Client, account_id : Integer, amount:Integer)
  Pre  "def": "(\<delta> c) and (\<delta> account_id) and (\<delta> amount)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and
                                                ((X .account_id) \<doteq> account_id) and
                                                (amount \<le>\<^sub>i\<^sub>n\<^sub>t (X .balance)) )"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A  = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                            ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance -\<^sub>i\<^sub>n\<^sub>t  amount)"


Context Bank :: get_balance (c : Client, account_id : Integer) : Integer
  Pre  "(\<delta> c) and (\<delta> account_id)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  client_exists: "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and
                                                              ((X .account_id) \<doteq> account_id))"
  Post spec: "let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                             ->any\<^sub>S\<^sub>e\<^sub>t()
              in  result \<triangleq> (A .balance)"
  Post frame: "(Set{} :: \<cdot>Set(\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>)) ->oclIsModifiedOnly()"

(* (* from this point, the SORRY flag in UML_OCL.thy
     (or declare [[quick_and_dirty = true]]) is currently
   needed for the following to work *)
lemma emptyFrame: "(\<sigma>,\<sigma>')   \<Turnstile> (Set{}->oclIsModifiedOnly()) \<Longrightarrow> \<sigma> = \<sigma>'"
sorry

lemma get_balance_is_query :
assumes  *: "(\<sigma>,\<sigma>')   \<Turnstile> ((bank :: \<cdot>Bank) .get_balance(c , a1) \<doteq> d)"
shows       "\<sigma> = \<sigma>'"
sorry

lemma dot__withdraw_defined_mono_strong :
         "\<tau> \<Turnstile> \<upsilon> (W .withdraw(X,Y,Z))
          \<Longrightarrow> (\<tau> \<Turnstile> \<delta> W) \<and> (\<tau> \<Turnstile> \<delta> X) \<and> (\<tau> \<Turnstile> \<delta> Y) \<and> (\<tau> \<Turnstile> \<delta> Z)"
sorry

lemma dot__deposit_defined_mono_strong :
         "\<tau> \<Turnstile> \<upsilon> (W .deposit(X,Y,Z))
          \<Longrightarrow> (\<tau> \<Turnstile> \<delta> W) \<and> (\<tau> \<Turnstile> \<delta> X) \<and> (\<tau> \<Turnstile> \<delta> Y) \<and> (\<tau> \<Turnstile> \<delta> Z)"
sorry

lemma dot__get_balance_defined_mono_strong :
         "\<tau> \<Turnstile> \<upsilon> (W .get_balance(X,Y))
          \<Longrightarrow> (\<tau> \<Turnstile> \<delta> W) \<and> (\<tau> \<Turnstile> \<delta> X) \<and> (\<tau> \<Turnstile> \<delta> Y)"
sorry

lemmas [simp,code_unfold] = dot_accessor
lemma
assumes const_bank : "const bank"
assumes const_c : "const c"
assumes const_a1 : "const a1"
assumes  *:   "(\<sigma>,\<sigma>')       \<Turnstile> ((bank :: \<cdot>Bank) .get_balance(c , a1) \<doteq> d)"
and      **:  "(\<sigma>',\<sigma>'')     \<Turnstile>  (bank .deposit(c, a1, a)    \<triangleq> null)"
and      ***: "(\<sigma>'',\<sigma>''')   \<Turnstile>  (bank .withdraw(c, a1, b)   \<triangleq> null)"
shows         "\<exists>\<sigma>''''. (\<sigma>''',\<sigma>'''') \<Turnstile> ((bank .get_balance(c , a1)) \<doteq> (d +\<^sub>i\<^sub>n\<^sub>t a -\<^sub>i\<^sub>n\<^sub>t b))"
proof -
have XXX: "\<And>\<tau> X. \<tau> \<Turnstile>  (X \<triangleq> null) \<Longrightarrow>  \<tau> \<Turnstile>  \<upsilon>(X)"
          by (metis foundation18 foundation22 valid2 valid_bool_split)
have YYY:  "\<And>\<tau> X. \<tau> \<Turnstile>  (X \<doteq> d) \<Longrightarrow>  \<tau> \<Turnstile>  \<upsilon>(X)"
          by (simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.defargs)
show "?thesis"
apply(insert * ** *** )
(* We get rid of the existential : since this is a query, putting \<sigma>'''' on \<sigma>''' is a good choice. *)
apply(rule_tac x = "\<sigma>'''" in exI)

(* first phase : we make all implicit definedness and validity knowledge explicit.
   I e we perform Delta-closure and exploit is_query's. *)
apply(frule get_balance_is_query, hypsubst)
apply(frule XXX) back
apply(drule dot__withdraw_defined_mono_strong, clarify)
apply(frule XXX)
apply(drule dot__deposit_defined_mono_strong, clarify)
apply(frule YYY)
apply(drule dot__get_balance_defined_mono_strong, clarify)
apply(frule get_balance_is_query, hypsubst)


apply(subst UML_OCL.dot__get_balance_Bank, subst OclValid_def, subst (2) StrongEq_def, subst true_def,
      simp only: option.inject eq_True Let_def)
apply(subgoal_tac "(\<sigma>''', \<sigma>'''') \<Turnstile> \<delta> bank \<and> (\<sigma>''', \<sigma>'''') \<Turnstile> \<upsilon> c \<and> (\<sigma>''', \<sigma>'''') \<Turnstile> \<upsilon> a1")
 prefer 2
 apply (meson const_OclValid1 const_OclValid2 const_a1 const_bank const_c)
apply(simp only: simp_thms if_True)

apply(subst (asm) UML_OCL.dot__get_balance_Bank, subst (asm) OclValid_def, subst (asm) (2) StrongEq_def, subst (asm) true_def,
      simp only: option.inject eq_True Let_def)
apply(subgoal_tac "(\<sigma>, \<sigma>') \<Turnstile> \<delta> bank \<and> (\<sigma>, \<sigma>') \<Turnstile> \<upsilon> c \<and> (\<sigma>, \<sigma>') \<Turnstile> \<upsilon> a1")
 prefer 2
 apply (meson const_OclValid1 const_OclValid2 const_a1 const_bank const_c)
apply(simp only: simp_thms if_True)
oops
*)

(* TODO : Use Locales. *)


find_theorems (100) "dot\<g>\<e>\<t>095\<b>\<a>\<l>\<a>\<n>\<c>\<e>"
find_theorems (100) name:"\<d>\<e>\<p>\<o>\<s>\<i>\<t>"

definition val2Mon :: "('\<sigma>, '\<alpha>::null)val \<Rightarrow>  ('\<alpha>,'\<sigma> state)MON\<^sub>S\<^sub>E"
where     "val2Mon f \<equiv> (\<lambda>\<sigma>. if \<exists>\<sigma>'. \<exists>d.  ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> d))
                             then Some(SOME(d,\<sigma>'). ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> (\<lambda>_. d))))
                             else None)"

definition "bind_SE' f1 f2 = bind_SE f1 (f2 o K)"

syntax    (xsymbols)
          "_bind_SE'" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E"
          ("(2 _ \<longleftarrow> _; _)" [5,8,8]8)
translations
          "x \<longleftarrow> f; g" == "CONST bind_SE' (CONST val2Mon (f)) (% x . g)"

lemma get_balanceE :
assumes 1: "\<sigma> \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r  \<longleftarrow> (self :: \<cdot>Bank) .get_balance(c , a1) ; M r)"
and     2: "(\<sigma>,\<sigma>')\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> a1))"
and     3: "\<sigma>' = \<sigma>"
and     4: "(\<sigma>,\<sigma>')\<Turnstile>(let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> a1))
                                        ->any\<^sub>S\<^sub>e\<^sub>t()
                    in  result  \<triangleq> (A .balance)) "
shows      "\<sigma>' \<Turnstile>\<^sub>M\<^sub>o\<^sub>n  (M (\<lambda>_. (result (\<sigma>,\<sigma>')))) "
oops

lemma get_balanceS :
assumes 1: "(\<sigma>,\<sigma>')\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> a1))"
and     2: "\<sigma>' = \<sigma>"
and     3: "(\<sigma>,\<sigma>')\<Turnstile>(let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> a1))
                                        ->any\<^sub>S\<^sub>e\<^sub>t()
                    in  result  \<triangleq> (A .balance)) "
shows      "(\<sigma> \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r  \<longleftarrow> (self :: \<cdot>Bank) .get_balance(c , a1) ; M r)) =
            (\<sigma>' \<Turnstile>\<^sub>M\<^sub>o\<^sub>n  (M (\<lambda>_. (result (\<sigma>,\<sigma>'))))) "
oops



lemma valid_sequence:
assumes client_account_defined : "\<forall> \<sigma> . (\<sigma>\<^sub>0, \<sigma>) \<Turnstile> bank .managed_accounts@pre->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> c and (X .account_id@pre \<doteq> a1))"
shows
           "\<sigma>\<^sub>0 \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r  \<longleftarrow> (bank :: \<cdot>Bank) .get_balance(c , a1) ;
                     _  \<longleftarrow> bank .deposit(c, a1, a) ;
                     _  \<longleftarrow> bank .withdraw(c , a1, b) ;
                     r' \<longleftarrow> bank .get_balance(c , a1) ;
                     assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  ((\<sigma>,\<sigma>) \<Turnstile> (r +\<^sub>i\<^sub>n\<^sub>t a -\<^sub>i\<^sub>n\<^sub>t b \<doteq> r'))))"
(*apply(subst get_balanceS)
apply(rule client_account_defined[THEN spec])
apply(rule refl)
apply(simp only:Let_def)
apply(rule UML_Logic.StrongEq_L_refl)
*)
oops

end
