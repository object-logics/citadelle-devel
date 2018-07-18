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

theory  UML_UnlimitedNatural
imports OCL.UML_PropertyProfiles
begin

section{* ... *}

text{* Unlike @{term "Integer"}, we should also include the infinity value besides @{term "undefined"} and @{term "null"}. *}


class      infinity = null +
   fixes   infinity :: "'a"
   assumes infinity_is_valid : "infinity \<noteq> bot"
   assumes infinity_is_defined : "infinity \<noteq> null"

instantiation   option  :: (null)infinity
begin
   definition infinity_option_def: "(infinity::'a::null option) \<equiv>  \<lfloor> null \<rfloor>"
   instance proof  show "(infinity::'a::null option) \<noteq> null"
                   by( simp add:infinity_option_def null_is_valid null_option_def bot_option_def)
                   show "(infinity::'a::null option) \<noteq> bot"
                   by( simp add:infinity_option_def null_option_def bot_option_def)
            qed
end

instantiation "fun"  :: (type,infinity) infinity
begin
 definition infinity_fun_def: "(infinity::'a \<Rightarrow> 'b::infinity) \<equiv> (\<lambda> x. infinity)"

 instance proof
            show "(infinity::'a \<Rightarrow> 'b::infinity) \<noteq> bot"
              apply(auto simp: infinity_fun_def bot_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: infinity_is_valid)
            done
            show "(infinity::'a \<Rightarrow> 'b::infinity) \<noteq> null"
              apply(auto simp: infinity_fun_def null_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: infinity_is_defined)
            done
          qed
end

type_synonym ('\<AA>,'\<alpha>) val' = "'\<AA> st \<Rightarrow> '\<alpha>::infinity"

definition limitedNatural :: "('\<AA>,'a::infinity)val' \<Rightarrow> ('\<AA>)Boolean" ("\<mu> _" [100]100)
where   "\<mu> X \<equiv>  \<lambda> \<tau> . if X \<tau> = bot \<tau> \<or> X \<tau> = null \<tau> \<or> X \<tau> = infinity \<tau> then false \<tau> else true \<tau>"

lemma (*valid*)[simp]: "\<upsilon> infinity = true"
  by(rule ext, simp add: bot_fun_def infinity_fun_def infinity_is_valid valid_def)

lemma (*defined*)[simp]: "\<delta> infinity = true"
  by(rule ext, simp add: bot_fun_def defined_def infinity_fun_def infinity_is_defined infinity_is_valid null_fun_def)

lemma (*limitedNatural*)[simp]: "\<mu> invalid = false"
  by(rule ext, simp add: bot_fun_def invalid_def limitedNatural_def)

lemma (*limitedNatural*)[simp]: "\<mu> null = false"
  by(rule ext, simp add: limitedNatural_def)

lemma (*limitedNatural*)[simp]: "\<mu> infinity = false"
  by(rule ext, simp add: limitedNatural_def)

section{* UML Types *}

text{* Since @{term "UnlimitedNatural"} is again a basic type, we define its semantic domain
as the valuations over @{typ "nat option option option"}. *}
type_synonym UnlimitedNatural\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "nat option option option"
type_synonym ('\<AA>)UnlimitedNatural = "('\<AA>, UnlimitedNatural\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val'"

section{* Basic Types UnlimitedNatural: Operations *}

subsection{* Fundamental Predicates on UnlimitedNaturals: Strict Equality *}

text{* The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Boolean"}-case as strict extension of the strong equality:*}
overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>)UnlimitedNatural,('\<AA>)UnlimitedNatural] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l[code_unfold] :
      "(x::('\<AA>)UnlimitedNatural) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y) \<tau>
                                    else invalid \<tau>"
end

text{* Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}*}
interpretation  StrictRefEq\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>)UnlimitedNatural) \<doteq> y"
         by unfold_locales (auto simp: StrictRefEq\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l)

subsection{* Basic UnlimitedNatural Constants *}

text{* Although the remaining part of this library reasons about
integers abstractly, we provide here as example some convenient shortcuts. *}

locale OclUnlimitedNatural

definition OclNat0 ::"('\<AA>)UnlimitedNatural" (*"\<zero>"*)
where      "OclNat0(*\<zero>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>0::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat1 ::"('\<AA>)UnlimitedNatural" (*"\<one>"*)
where      "OclNat1(*\<one>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>1::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat2 ::"('\<AA>)UnlimitedNatural" (*"\<two>"*)
where      "OclNat2(*\<two>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>2::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat3 ::"('\<AA>)UnlimitedNatural" (*"\<three>"*)
where      "OclNat3(*\<three>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>3::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat4 ::"('\<AA>)UnlimitedNatural" (*"\<four>"*)
where      "OclNat4(*\<four>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>4::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat5 ::"('\<AA>)UnlimitedNatural" (*"\<five>"*)
where      "OclNat5(*\<five>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>5::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat6 ::"('\<AA>)UnlimitedNatural" (*"\<six>"*)
where      "OclNat6(*\<six>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>6::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat7 ::"('\<AA>)UnlimitedNatural" (*"\<seven>"*)
where      "OclNat7(*\<seven>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>7::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat8 ::"('\<AA>)UnlimitedNatural" (*"\<eight>"*)
where      "OclNat8(*\<eight>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>8::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat9 ::"('\<AA>)UnlimitedNatural" (*"\<nine>"*)
where      "OclNat9(*\<nine>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>9::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat10 ::"('\<AA>)UnlimitedNatural" (*"\<one>\<zero>"*)
where      "OclNat10(*\<one>\<zero>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>10::nat\<rfloor>\<rfloor>\<rfloor>)"

context OclUnlimitedNatural
begin

abbreviation OclNat_0 ("\<zero>") where "\<zero> \<equiv> OclNat0"
abbreviation OclNat_1 ("\<one>") where "\<one> \<equiv> OclNat1"
abbreviation OclNat_2 ("\<two>") where "\<two> \<equiv> OclNat2"
abbreviation OclNat_3 ("\<three>") where "\<three> \<equiv> OclNat3"
abbreviation OclNat_4 ("\<four>") where "\<four> \<equiv> OclNat4"
abbreviation OclNat_5 ("\<five>") where "\<five> \<equiv> OclNat5"
abbreviation OclNat_6 ("\<six>") where "\<six> \<equiv> OclNat6"
abbreviation OclNat_7 ("\<seven>") where "\<seven> \<equiv> OclNat7"
abbreviation OclNat_8 ("\<eight>") where "\<eight> \<equiv> OclNat8"
abbreviation OclNat_9 ("\<nine>") where "\<nine> \<equiv> OclNat9"
abbreviation OclNat_10 ("\<one>\<zero>") where "\<one>\<zero> \<equiv> OclNat10"

end

definition OclNat_infinity :: "('\<AA>)UnlimitedNatural" ("\<infinity>")
where "\<infinity> = (\<lambda>_. \<lfloor>\<lfloor>None\<rfloor>\<rfloor>)"

subsection{* Validity and Definedness Properties *}

lemma  "\<delta>(null::('\<AA>)UnlimitedNatural) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)UnlimitedNatural) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

lemma [simp,code_unfold]: "\<mu> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp add: limitedNatural_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def infinity_fun_def infinity_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> OclNat0 = true" by(simp add:OclNat0_def)
lemma [simp,code_unfold]: "\<upsilon> OclNat0 = true" by(simp add:OclNat0_def)


subsection{* Arithmetical Operations *}

subsubsection{* Definition *}
text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot). *}
text{* Note that we can not follow the lexis of the OCL Standard for Isabelle
technical reasons; these operators are heavily overloaded in the HOL library
that a further overloading would lead to heavy technical buzz in this
document.
*}
definition OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "+\<^sub>n\<^sub>a\<^sub>t" 40)
where "x +\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> + \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>
                else invalid \<tau> "
interpretation OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(+\<^sub>n\<^sub>a\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x\<rceil>\<rceil>\<rceil> + \<lceil>\<lceil>\<lceil>y\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>"
         apply (unfold_locales, auto simp:OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def bot_option_def null_option_def infinity_option_def)
         sorry
(* TODO: special locale setup.*)


definition OclMinus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "-\<^sub>n\<^sub>a\<^sub>t" 41)
where "x -\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> - \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclMinus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(-\<^sub>n\<^sub>a\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x\<rceil>\<rceil>\<rceil> - \<lceil>\<lceil>\<lceil>y\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>"
         apply (unfold_locales, auto simp:OclMinus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def bot_option_def null_option_def infinity_option_def)
         sorry
(* TODO: special locale setup.*)


definition OclMult\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "*\<^sub>n\<^sub>a\<^sub>t" 45)
where "x *\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> * \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclMult\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "( *\<^sub>n\<^sub>a\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x\<rceil>\<rceil>\<rceil> * \<lceil>\<lceil>\<lceil>y\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>"
         apply (unfold_locales, auto simp:OclMult\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def bot_option_def null_option_def infinity_option_def)
         sorry
(* TODO: special locale setup.*)

text{* Here is the special case of division, which is defined as invalid for division
by zero. *}
definition OclDivision\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "div\<^sub>n\<^sub>a\<^sub>t" 45)
where "x div\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclNat0 \<tau> then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> div \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor> else invalid \<tau>
                       else invalid \<tau> "
(* TODO: special locale setup.*)


definition OclModulus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "mod\<^sub>n\<^sub>a\<^sub>t" 45)
where "x mod\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclNat0 \<tau> then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> mod \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor> else invalid \<tau>
                       else invalid \<tau> "
(* TODO: special locale setup.*)


definition OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>n\<^sub>a\<^sub>t" 35)
where "x <\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> < \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then (\<mu> x) \<tau>
                else invalid \<tau>"
interpretation OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(<\<^sub>n\<^sub>a\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x\<rceil>\<rceil>\<rceil> < \<lceil>\<lceil>\<lceil>y\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>"
         apply (unfold_locales, auto simp:OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def bot_option_def null_option_def infinity_option_def)
         oops
(* TODO: special locale setup.*)

definition OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>n\<^sub>a\<^sub>t" 35)
where "x \<le>\<^sub>n\<^sub>a\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> \<le> \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then not (\<mu> y) \<tau>
                else invalid \<tau>"
interpretation OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(\<le>\<^sub>n\<^sub>a\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x\<rceil>\<rceil>\<rceil> \<le> \<lceil>\<lceil>\<lceil>y\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>"
         apply (unfold_locales, auto simp:OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def bot_option_def null_option_def infinity_option_def)
         oops
(* TODO: special locale setup.*)

abbreviation OclAdd_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "+\<^sub>U\<^sub>N" 40) where "x +\<^sub>U\<^sub>N y \<equiv> OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclMinus_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "-\<^sub>U\<^sub>N" 41) where "x -\<^sub>U\<^sub>N y \<equiv> OclMinus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclMult_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "*\<^sub>U\<^sub>N" 45) where "x *\<^sub>U\<^sub>N y \<equiv> OclMult\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclDivision_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "div\<^sub>U\<^sub>N" 45) where "x div\<^sub>U\<^sub>N y \<equiv> OclDivision\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclModulus_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "mod\<^sub>U\<^sub>N" 45) where "x mod\<^sub>U\<^sub>N y \<equiv> OclModulus\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclLess_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "<\<^sub>U\<^sub>N" 35) where "x <\<^sub>U\<^sub>N y \<equiv> OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclLe_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "\<le>\<^sub>U\<^sub>N" 35) where "x \<le>\<^sub>U\<^sub>N y \<equiv> OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"

subsubsection{* Basic Properties *}

lemma OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_commute: "(X +\<^sub>n\<^sub>a\<^sub>t Y) = (Y +\<^sub>n\<^sub>a\<^sub>t X)"
  by(rule ext,auto simp:true_def false_def OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def invalid_def
                   split: option.split option.split_asm
                          bool.split bool.split_asm)

subsubsection{* Execution with Invalid or Null or Zero as Argument *}

lemma OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_zero1[simp,code_unfold] :
"(x +\<^sub>n\<^sub>a\<^sub>t OclNat0) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 proof (rule ext, rename_tac \<tau>, case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  fix \<tau> show "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau> \<Longrightarrow>
              (x +\<^sub>n\<^sub>a\<^sub>t OclNat0) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_true', simp add: OclValid_def)
  sorry
 next fix \<tau>
  have A: "\<And>\<tau>. (\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))) = (x \<tau> = invalid \<tau> \<or> \<tau> \<Turnstile> \<delta> x)"
  by (metis OclNot_not OclOr_def defined5 defined6 defined_not_I foundation11 foundation18'
            foundation6 foundation7 foundation9 invalid_def)
  have B: "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> = x \<tau>"
   apply(cases "x \<tau>", metis bot_option_def foundation16)
   apply(rename_tac x', case_tac x', metis bot_option_def foundation16 null_option_def)
  by(simp)
  show "(x +\<^sub>n\<^sub>a\<^sub>t OclNat0) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
    when "\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))"
   apply(insert that, subst OclIf_false', simp, simp add: A, auto simp: OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_def OclNat0_def)
     (* *)
  sorry
  apply_end(metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)
oops

lemma OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_zero2[simp,code_unfold] :
"(OclNat0 +\<^sub>n\<^sub>a\<^sub>t x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
apply(subst OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l_commute, simp?)
oops

(* TODO Basic proproperties for multiplication, division, modulus. *)



subsubsection{* Test Statements *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

context OclUnlimitedNatural
begin
Assert_local "\<tau> \<Turnstile> ( \<nine> \<le>\<^sub>U\<^sub>N \<one>\<zero> )"
Assert_local "\<tau> \<Turnstile> (( \<four> +\<^sub>U\<^sub>N \<four> ) \<le>\<^sub>U\<^sub>N \<one>\<zero> )"
Assert_local "\<tau> |\<noteq> (( \<four> +\<^sub>U\<^sub>N ( \<four> +\<^sub>U\<^sub>N \<four> )) <\<^sub>U\<^sub>N \<one>\<zero> )"
Assert_local "\<tau> \<Turnstile> (\<zero> \<le>\<^sub>n\<^sub>a\<^sub>t \<infinity>)"
Assert_local "\<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>U\<^sub>N \<one>))"
Assert_local "\<tau> \<Turnstile> not (\<upsilon> (\<infinity> +\<^sub>n\<^sub>a\<^sub>t \<zero>))"
Assert_local "\<tau> \<Turnstile>      \<mu> \<one>"
end
Assert "\<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>n\<^sub>a\<^sub>t \<infinity>))"
Assert "\<tau> \<Turnstile> not (\<infinity> <\<^sub>n\<^sub>a\<^sub>t \<infinity>)"
Assert "\<tau> \<Turnstile> not (\<upsilon> (invalid \<le>\<^sub>n\<^sub>a\<^sub>t \<infinity>))"
Assert "\<tau> \<Turnstile> not (\<upsilon> (null \<le>\<^sub>n\<^sub>a\<^sub>t \<infinity>))"
Assert "\<tau> \<Turnstile>      \<upsilon> \<infinity>"
Assert "\<tau> \<Turnstile>      \<delta> \<infinity>"
Assert "\<tau> \<Turnstile> not (\<mu> \<infinity>)"



lemma integer_non_null [simp]: "((\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) \<doteq> (null::('\<AA>)UnlimitedNatural)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma null_non_integer [simp]: "((null::('\<AA>)UnlimitedNatural) \<doteq> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma OclNat0_non_null [simp,code_unfold]: "(OclNat0 \<doteq> null) = false" by(simp add: OclNat0_def)
lemma null_non_OclNat0 [simp,code_unfold]: "(null \<doteq> OclNat0) = false" by(simp add: OclNat0_def)


subsection{* Test Statements on Basic UnlimitedNatural *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}


text{* Elementary computations on UnlimitedNatural *}

Assert "\<tau> \<Turnstile> OclNat0 <> OclNat1"
Assert "\<tau> \<Turnstile> OclNat1 <> OclNat0"
Assert "\<tau> \<Turnstile> OclNat0 \<doteq> OclNat0"

Assert "\<tau> \<Turnstile> \<upsilon> OclNat0"
Assert "\<tau> \<Turnstile> \<delta> OclNat0"
Assert "\<tau> \<Turnstile> \<upsilon> (null::('\<AA>)UnlimitedNatural)"
Assert "\<tau> \<Turnstile> (invalid \<triangleq> invalid)"
Assert "\<tau> \<Turnstile> (null \<triangleq> null)"
Assert "\<tau> |\<noteq> (invalid \<doteq> (invalid::('\<AA>)UnlimitedNatural))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)UnlimitedNatural))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> (invalid <> (invalid::('\<AA>)UnlimitedNatural))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid <> (invalid::('\<AA>)UnlimitedNatural))" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)UnlimitedNatural) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)UnlimitedNatural) )" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> (OclNat0 <\<^sub>n\<^sub>a\<^sub>t null)"
Assert "\<tau> |\<noteq> (\<delta> (OclNat0 <\<^sub>n\<^sub>a\<^sub>t null))"


end
