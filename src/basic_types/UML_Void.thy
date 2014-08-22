(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Void.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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
(* $Id:$ *)

theory  UML_Void
imports UML_Boolean
begin

section{* Basic Type Void *}

(* For technical reasons, the type does not contain to the null-class yet. *)
text {* This \emph{minimal} OCL type contains only two elements:
@{term "invalid"} and @{term "null"}.
@{term "Void"} could initially be defined as @{typ "unit option option"},
however the cardinal of this type is more than two, so it would have the cost to consider
 @{text "Some None"} and @{text "Some (Some ())"} seemingly everywhere.*}
 
subsection{* Fundamental Properties on Basic Types: Strict Equality *}

subsubsection{* Definition *}

instantiation   Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: bot
begin
   definition bot_Void_def: "(bot_class.bot :: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x:: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Void_def, subst Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: null_option_def bot_option_def)
                  done
            qed
end

instantiation   Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e :: null
begin
   definition null_Void_def: "(null::Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null:: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  apply(simp add:null_Void_def bot_Void_def, subst Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: null_option_def bot_option_def)
                  done
            qed
end


text{* The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Void"}-case as strict extension of the strong equality:*}
defs   StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d[code_unfold] :
      "(x::('\<AA>)Void) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                 then (x \<triangleq> y) \<tau>
                                 else invalid \<tau>"
text{* Property proof in terms of @{term "profile_bin3"}*}
interpretation   StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d : profile_bin3 "\<lambda> x y. (x::('\<AA>)Void) \<doteq> y" 
       by unfold_locales (auto simp:  StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d)
 
                                    
subsection{* Test Statements *}

Assert "\<tau> \<Turnstile> ((null::('\<AA>)Void)  \<doteq> null)"


end