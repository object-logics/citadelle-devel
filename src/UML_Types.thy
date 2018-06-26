(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Types.thy --- Types definitions.
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

chapter{* Formalization I: OCL Types and Core Definitions \label{sec:focl-types}*}

theory    UML_Types
imports   HOL.Transcendental (* Testing *)
keywords "Assert" :: thy_decl
     and "Assert_local" :: thy_decl
begin

(* declare[[syntax_ambiguity_warning = false]] *)

section{* Preliminaries *}
subsection{* Notations for the Option Type *}

text{*
  First of all, we will use a more compact notation for the library
  option type which occur all over in our definitions and which will make
  the presentation more like a textbook:
*}

no_notation ceiling  ("\<lceil>_\<rceil>") (* For Real Numbers only ... Otherwise has unfortunate side-effects on syntax. *)
no_notation floor  ("\<lfloor>_\<rfloor>") (* For Real Numbers only ... Otherwise has unfortunate side-effects on syntax. *)

type_notation option ("\<langle>_\<rangle>\<^sub>\<bottom>") (* NOTE: "_\<^sub>\<bottom>" also works *)
notation Some ("\<lfloor>(_)\<rfloor>")
notation None ("\<bottom>")
notation the ("\<lceil>(_)\<rceil>")

text{* These commands introduce an alternative, more compact notation for the type constructor
 @{typ "'\<alpha> option"}, namely @{typ "\<langle>'\<alpha>\<rangle>\<^sub>\<bottom>"}. Furthermore, the constructors @{term "Some X"} and
 @{term "None"} of the type @{typ "'\<alpha> option"}, namely @{term "\<lfloor>X\<rfloor>"} and @{term "\<bottom>"}. *}

text{* The definitions for the constants and operations based on functions
will be geared towards a format that Isabelle can check to be a ``conservative''
(\ie, logically safe) axiomatic definition. By introducing an explicit
interpretation function (which happens to be defined just as the identity
since we are using a shallow embedding of OCL into HOL), all these definitions
can be rewritten into the conventional semantic textbook format.
To say it in other words: The interpretation function @{text Sem} as defined
below is just a textual marker for presentation purposes, i.e. intended for readers
used to conventional textbook notations on semantics. Since we use a ``shallow embedding'',
i.e. since we represent the syntax of OCL directly by HOL constants, the interpretation function
is semantically not only superfluous, but from an Isabelle perspective strictly in
the way for certain consistency checks performed by the definitional packages.
*}

definition Sem :: "'a \<Rightarrow> 'a" ("I\<lbrakk>_\<rbrakk>")
where "I\<lbrakk>x\<rbrakk> \<equiv> x"


subsection{*  Common Infrastructure for all OCL Types \label{sec:focl-common-types}*}

text {* In order to have the possibility to nest collection types,
  such that we can give semantics to expressions like @{text "Set{Set{\<two>},null}"},
  it is necessary to introduce a uniform interface for types having
  the @{text "invalid"} (= bottom) element. The reason is that we impose
  a data-invariant on raw-collection \inlineisar|types_code| which assures
  that the @{text "invalid"} element is not allowed inside the collection;
  all raw-collections of this form were identified with the @{text "invalid"} element
  itself. The construction requires that the new collection type is
  not comparable with the raw-types (consisting of nested option type constructions),
  such that the data-invariant must be expressed in terms of the interface.
  In a second step, our base-types will be shown to be instances of this interface.
 *}

text{*
  This uniform interface consists in a type class requiring the existence
  of a bot and a null element. The construction proceeds by
  abstracting the null (defined by @{text "\<lfloor> \<bottom> \<rfloor>"} on
  @{text "'a option option"}) to a @{text null} element, which may
  have an arbitrary semantic structure, and an undefinedness element @{text "\<bottom>"}
  to an abstract undefinedness element @{text "bot"} (also written
  @{text "\<bottom>"} whenever no confusion arises). As a consequence, it is necessary
  to redefine the notions of invalid, defined, valuation etc.
  on top of this interface. *}

text{*
  This interface consists in two abstract type classes @{text bot}
  and @{text null} for the class of all types comprising a bot and a
  distinct null element.  *}
(*
instance option   :: (plus) plus  by intro_classes
instance "fun"    :: (type, plus) plus by intro_classes
*)

class   bot =
   fixes   bot :: "'a"
   assumes nonEmpty : "\<exists> x. x \<noteq> bot"


class      null = bot +
   fixes   null :: "'a"
   assumes null_is_valid : "null \<noteq> bot"


subsection{* Accommodation of Basic Types to the Abstract Interface *}

text{*
  In the following it is shown that the ``option-option'' type is
  in fact in the @{text null} class and that function spaces over these
  classes again ``live'' in these classes. This motivates the default construction
  of the semantic domain for the basic types (\inlineocl{Boolean},
  \inlineocl{Integer}, \inlineocl{Real}, \ldots).
*}

instantiation   option  :: (type)bot
begin
   definition bot_option_def: "(bot::'a option) \<equiv> (None::'a option)"
   instance proof show        "\<exists>x::'a option. x \<noteq> bot"
                  by(rule_tac x="Some x" in exI, simp add:bot_option_def)
            qed
end


instantiation   option  :: (bot)null
begin
   definition null_option_def: "(null::'a::bot option) \<equiv>  \<lfloor> bot \<rfloor>"
   instance proof  show        "(null::'a::bot option) \<noteq> bot"
                   by( simp add : null_option_def bot_option_def)
            qed
end


instantiation "fun"  :: (type,bot) bot
begin
   definition bot_fun_def: "bot \<equiv> (\<lambda> x. bot)"
   instance proof  show "\<exists>(x::'a \<Rightarrow> 'b). x \<noteq> bot"
                   apply(rule_tac x="\<lambda> _. (SOME y. y \<noteq> bot)" in exI, auto)
                   apply(drule_tac x=x in fun_cong,auto simp:bot_fun_def)
                   apply(erule contrapos_pp, simp)
                   apply(rule some_eq_ex[THEN iffD2])
                   apply(simp add: nonEmpty)
                   done
            qed
end


instantiation "fun"  :: (type,null) null
begin
 definition null_fun_def: "(null::'a \<Rightarrow> 'b::null) \<equiv> (\<lambda> x. null)"
 instance proof
              show "(null::'a \<Rightarrow> 'b::null) \<noteq> bot"
              apply(auto simp: null_fun_def bot_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: null_is_valid)
            done
          qed
end

text{* A trivial consequence of this adaption of the interface is that
abstract and concrete versions of null are the same on base types
(as could be expected). *}

subsection{* The Common Infrastructure of Object Types (Class Types) and States. *}

text{* Recall that OCL is a textual extension of the UML; in particular, we use OCL as means to
annotate UML class models. Thus, OCL inherits a notion of \emph{data} in the UML: UML class
models provide classes, inheritance, types of objects, and subtypes connecting them along
the inheritance hierarchie.
*}

text{* For the moment, we formalize the most common notions of objects, in particular
the existance of object-identifiers (oid) for each object under which it can
be referenced in a \emph{state}. *}

type_synonym oid = nat

text{* We refrained from the alternative:
\begin{isar}[mathescape]
$\text{\textbf{type-synonym}}$ $\mathit{oid = ind}$
\end{isar}
which is slightly more abstract but non-executable.
*}

text{* \emph{States} in UML/OCL are a pair of
\begin{itemize}
\item a partial map from oid's to elements of an \emph{object universe},
      \ie{} the set of all possible object representations.
\item and an oid-indexed family of \emph{associations}, \ie{} finite relations between
      objects living in a state. These relations can be n-ary which we model by nested lists.
\end{itemize}
For the moment we do not have to describe the concrete structure of the object universe and denote
it by the  polymorphic variable @{text "'\<AA>"}.*}

record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid \<rightharpoonup> ((oid list) list) list"

text{* In general, OCL operations are functions implicitly depending on a pair
of pre- and post-state, \ie{} \emph{state transitions}. Since this will be reflected in our
representation of OCL Types within HOL, we need to introduce the foundational concept of an
object id (oid), which is just some infinite set, and some abstract notion of state. *}

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

text{* We will require for all objects that there is a function that
projects the oid of an object in the state (we will settle the question how to define
this function later). We will use the Isabelle type class mechanism~\cite{haftmann.ea:constructive:2006}
to capture this: *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"

text{* The major instance needed are instances constructed over options: once an object,
options of objects are also objects. *}
instantiation   option  :: (object)object
begin
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end


subsection{* Common Infrastructure for all OCL Types (II): Valuations as OCL Types *}
text{* Since OCL operations in general depend on pre- and post-states, we will
represent OCL types as \emph{functions} from pre- and post-state to some
HOL raw-type that contains exactly the data in the OCL type --- see below.
This gives rise to the idea that we represent OCL types by \emph{Valuations}.
*}
text{* Valuations are functions from a state pair (built upon
data universe @{typ "'\<AA>"}) to an arbitrary null-type (\ie, containing
at least a destinguished @{text "null"} and @{text "invalid"} element). *}

type_synonym ('\<AA>,'\<alpha>) val = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* The definitions for the constants and operations based on valuations
will be geared towards a format that Isabelle can check to be a ``conservative''
(\ie, logically safe) axiomatic definition. By introducing an explicit
interpretation function (which happens to be defined just as the identity
since we are using a shallow embedding of OCL into HOL), all these definitions
can be rewritten into the conventional semantic textbook format  as follows: *}

subsection{* The fundamental constants 'invalid' and 'null' in all OCL Types *}

text{* As a consequence of semantic domain definition, any OCL type will
have the two semantic constants @{text "invalid"} (for exceptional, aborted
computation) and @{text "null"}:
 *}

definition invalid :: "('\<AA>,'\<alpha>::bot) val"
where     "invalid \<equiv> \<lambda> \<tau>. bot"

text{* This conservative Isabelle definition of the polymorphic constant
@{const invalid} is equivalent with the textbook definition: *}

lemma textbook_invalid: "I\<lbrakk>invalid\<rbrakk>\<tau> = bot"
by(simp add: invalid_def Sem_def)


text {* Note that the definition :
{\small
\begin{isar}[mathescape]
definition null    :: "('$\mathfrak{A}$,'\<alpha>::null) val"
where     "null    \<equiv> \<lambda> \<tau>. null"
\end{isar}
} is not  necessary since we defined the entire function space over null types
again as null-types; the crucial definition is @{thm "null_fun_def"}.
Thus, the polymorphic constant @{const null} is simply the result of
a general type class construction. Nevertheless, we can derive the
semantic textbook definition for the OCL null constant based on the
abstract null:
*}

lemma textbook_null_fun: "I\<lbrakk>null::('\<AA>,'\<alpha>::null) val\<rbrakk> \<tau> = (null::('\<alpha>::null))"
by(simp add: null_fun_def Sem_def)

section{* Basic OCL Value Types *}

text {* The structure of this section roughly follows the structure of Chapter
11 of the OCL standard~\cite{omg:ocl:2012}, which introduces the OCL
Library. *}

text{* The semantic domain of the (basic) boolean type is now defined as the Standard:
the space of valuation to @{typ "bool option option"}, \ie{} the Boolean base type:*}

type_synonym Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "bool option option"
type_synonym ('\<AA>)Boolean = "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Because of the previous class definitions, Isabelle type-inference establishes that
@{typ "('\<AA>)Boolean"} lives actually both in the type class @{term bot} and @{term null};
this type is sufficiently rich to contain at least these two elements.
Analogously we build: *}
type_synonym Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "int option option"
type_synonym ('\<AA>)Integer = "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

type_synonym String\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "string option option"
type_synonym ('\<AA>)String = "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

type_synonym Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "real option option"
type_synonym ('\<AA>)Real = "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Since @{term "Real"} is again a basic type, we define its semantic domain
as the valuations over @{text "real option option"} --- i.e. the mathematical type of real numbers.
The HOL-theory for @{text real} ``Real'' transcendental numbers such as $\pi$ and $e$ as well as
infrastructure to reason over infinite convergent Cauchy-sequences (it is thus possible, in principle,
to reason in Featherweight OCL that the sum of inverted two-s exponentials is actually 2.

If needed, a code-generator to compile @{text "Real"} to floating-point
numbers can be added; this allows for mapping reals to an efficient machine representation;
of course, this feature would be logically unsafe.*}

text{* For technical reasons related to the Isabelle type inference for type-classes
(we don't get the properties in the right order that class instantiation provides them,
if we would follow the previous scheme), we give a slightly atypic definition:*}

typedef Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "{X::unit option option. X = bot \<or> X = null }" by(rule_tac x="bot" in exI, simp)

type_synonym ('\<AA>)Void = "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"




section{* Some OCL Collection Types *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, \ie, the type should not
      contain junk-elements that are not representable by OCL expressions, and
\item we want a possibility to nest collection types (so, we want the
      potential of talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}).
\end{enumerate}
The former principle rules out the option to define @{text "'\<alpha> Set"} just by
 @{text "('\<AA>, ('\<alpha> option option) set) val"}. This would allow sets to contain
junk elements such as @{text "{\<bottom>}"} which we need to identify with undefinedness
itself. Abandoning fully abstractness of rules would later on produce all sorts
of problems when quantifying over the elements of a type.
However, if we build an own type, then it must conform to our abstract interface
in order to have nested types: arguments of type-constructors must conform to our
abstract interface, and the result type too.
*}

subsection{* The Construction of the Pair Type (Tuples) *}

text{* The core of an own type construction is done via a type
  definition which provides the base-type @{text "('\<alpha>, '\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef (overloaded) ('\<alpha>, '\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "{X::('\<alpha>::null \<times> '\<beta>::null) option option.
                                           X = bot \<or> X = null \<or> (fst\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot \<and> snd\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot)}"
                            by (rule_tac x="bot" in exI, simp)

text{* We ``carve'' out from the concrete type @{typ "('\<alpha>::null \<times> '\<beta>::null) option option"}
the new fully abstract type, which will not contain representations like @{term "\<lfloor>\<lfloor>(\<bottom>,a)\<rfloor>\<rfloor>"}
or @{term "\<lfloor>\<lfloor>(b,\<bottom>)\<rfloor>\<rfloor>"}. The type constuctor @{text "Pair{x,y}"} to be defined later will
identify these with @{term "invalid"}.
*}

instantiation   Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null,null)bot
begin
   definition bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(bot_class.bot :: ('a::null,'b::null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x::('a,'b) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  by(simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def  Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject  null_option_def bot_option_def)
            qed
end

instantiation   Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null,null)null
begin
   definition null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null,'b::null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null,'b::null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  by(simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                               null_option_def bot_option_def)
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>,'\<beta>) Pair  = "('\<AA>, ('\<alpha>,'\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_notation   Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e ("Pair'(_,_')")

subsection{* The Construction of the Set Type *}

text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "'\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. Note that we make
  no restriction whatsoever to \emph{finite} sets; while with
  the standards type-constructors only finite sets can be denoted,
  there is the possibility to define in fact infinite
  type constructors in \FOCL (c.f. \autoref{sec:set-type-extensions}). *}

typedef (overloaded) '\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ="{X::('\<alpha>::null) set option option. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by (rule_tac x="bot" in exI, simp)

instantiation   Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)bot
begin

   definition bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(bot::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x::'a Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  by(simp add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject null_option_def bot_option_def)
            qed
end

instantiation   Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)null
begin

   definition null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  by(simp add:null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                              null_option_def bot_option_def)
            qed
end

text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_notation   Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ("Set'(_')")

subsection{* The Construction of the Bag Type *}
text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "'\<alpha> Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}
  based on multi-sets from the \HOL library. As in Sets, it
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section, and as in sets, we make
  no restriction whatsoever to \emph{finite} multi-sets; while with
  the standards type-constructors only finite sets can be denoted,
  there is the possibility to define in fact infinite
  type constructors in \FOCL (c.f. \autoref{sec:bag-type-extensions}).
  However, while several @{text null} elements are possible in a Bag, there
  can't be no bottom (invalid) element in them.
*}

typedef (overloaded) '\<alpha> Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e ="{X::('\<alpha>::null \<Rightarrow> nat) option option. X = bot \<or> X = null \<or> \<lceil>\<lceil>X\<rceil>\<rceil> bot = 0 }"
          by (rule_tac x="bot" in exI, simp)

instantiation   Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)bot
begin

   definition bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(bot::('a::null) Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x::'a Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  by(simp add: bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                               null_option_def bot_option_def)
            qed
end

instantiation   Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)null
begin

   definition null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null) Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  by(simp add:null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                              null_option_def bot_option_def)
            qed
end

text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Bag  = "('\<AA>, '\<alpha> Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_notation   Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e ("Bag'(_')")

subsection{* The Construction of the Sequence Type *}

text{* The core of an own type construction is done via a type
  definition which provides the base-type @{text "'\<alpha> Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef (overloaded) '\<alpha> Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e ="{X::('\<alpha>::null) list option option.
                                        X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by (rule_tac x="bot" in exI, simp)

instantiation   Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)bot
begin

   definition bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(bot::('a::null) Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x::'a Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  by(auto simp:bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                               null_option_def bot_option_def)
            qed
end


instantiation   Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)null
begin

   definition null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null) Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  by(auto simp:bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject
                               null_option_def bot_option_def)
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Sequence  = "('\<AA>, '\<alpha> Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_notation   Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e ("Sequence'(_')")

subsection{* Discussion: The Representation of UML/OCL Types in Featherweight OCL *}
text{* In the introduction, we mentioned that there is an ``injective representation
mapping'' between the types of OCL and the types of Featherweight OCL (and its
meta-language: HOL). This injectivity is at the heart of our representation technique
--- a so-called \emph{shallow embedding} --- and means: OCL types were mapped one-to-one
to types in HOL, ruling out a resentation where
everything is mapped on some common HOL-type, say ``OCL-expression'', in which we
would have to sort out the typing of OCL and its impact on the semantic representation
function in an own, quite heavy side-calculus.
*}

text{* After the previous sections, we are now able to exemplify this representation as follows:

\begin{table}[htbp]
   \centering
   \begin{tabu}{lX[,c,]}
      \toprule
      OCL Type & HOL Type \\
      \midrule
      \inlineocl|Boolean|  & @{typ  "('\<AA>)Boolean"} \\
      \inlineocl|Boolean -> Boolean| & @{typ  "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"} \\
      \inlineocl|(Integer,Integer) -> Boolean| & @{typ  "('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean"} \\
      \inlineocl|Set(Integer)| & @{typ "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e)Set"} \\
      \inlineocl|Set(Integer)-> Real| & @{typ "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e)Set \<Rightarrow> ('\<AA>)Real"} \\
      \inlineocl|Set(Pair(Integer,Boolean))| & @{typ "('\<AA>,(Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e)Set"} \\
      \inlineocl|Set(<T>)| & @{typ "('\<AA>,'\<alpha>::null)Set"} \\
      \bottomrule
   \end{tabu}
   \caption{Correspondance between \OCL types and \HOL types}
   \label{tab:types}
\end{table}
We do not formalize the representation map here; however, its principles are quite straight-forward:
\begin{enumerate}
\item cartesion products of arguments were curried,
\item constants of type \inlineocl{T} were mapped to valuations over the
      HOL-type for \inlineocl{T},
\item functions \inlineocl{T -> T'} were mapped to functions in HOL, where
      \inlineocl{T} and  \inlineocl{T'}  were mapped to the valuations for them, and
\item the arguments of type constructors  \inlineocl{Set(T)} remain corresponding HOL base-types.
\end{enumerate}

*}

text{* Note, furthermore, that our construction of ``fully abstract types'' (no junk, no confusion)
assures that the logical equality to be defined in the next section works correctly and comes
as element of the ``lingua franca'', \ie{} HOL. *}

(*<*)
section{* Miscelleaneous: ML assertions *}
text{* \fixme{Can we suppress this form the text ???} *}
text{* We introduce here a new command \emph{Assert} similar as \emph{value} for proving
 that the given term in argument is a true proposition. The difference with \emph{value} is that
\emph{Assert} fails if the normal form of the term evaluated is not equal to @{term True}.
Moreover, in case \emph{value} could not normalize the given term, as another strategy of reduction
 we try to prove it with a single ``simp'' tactic. *}

ML{*
fun disp_msg title msg status = title ^ ": '" ^ msg ^ "' " ^ status

fun lemma msg specification_theorem concl in_local thy =
  SOME
    (in_local (fn lthy =>
           specification_theorem Thm.theoremK NONE (K I) Binding.empty_atts [] []
             (Element.Shows [(Binding.empty_atts, [(concl lthy, [])])])
             false lthy
        |> Proof.global_terminal_proof
             ((Method.Combinator ( Method.no_combinator_info
                                 , Method.Then
                                 , [Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac ctxt 1))]),
               (Position.none, Position.none)), NONE))
              thy)
  handle ERROR s =>
    (warning s; writeln (disp_msg "KO" msg "failed to normalize"); NONE)

fun outer_syntax_command command_spec theory in_local =
  Outer_Syntax.command command_spec "assert that the given specification is true"
    (Parse.term >> (fn elems_concl => theory (fn thy =>
      case
        lemma "nbe" (Specification.theorem true)
          (fn lthy =>
            let val expr = Nbe.dynamic_value lthy (Syntax.read_term lthy elems_concl)
                val thy = Proof_Context.theory_of lthy
                open HOLogic in
            if Sign.typ_equiv thy (fastype_of expr, @{typ "prop"}) then
              expr
            else mk_Trueprop (mk_eq (@{term "True"}, expr))
            end)
          in_local
          thy
      of  NONE =>
            let val attr_simp = "simp" in
            case lemma attr_simp (Specification.theorem_cmd true) (K elems_concl) in_local thy of
               NONE => raise (ERROR "Assertion failed")
             | SOME thy =>
                (writeln (disp_msg "OK" "simp" "finished the normalization");
(* TO BE DONE
   why does this not work ? ? ?
   une regle importante est dans simp, mais pas dans code_unfold ... *)
                 thy)
            end
        | SOME thy => thy)))

val () = outer_syntax_command @{command_keyword Assert} Toplevel.theory Named_Target.theory_map
val () = outer_syntax_command @{command_keyword Assert_local} (Toplevel.local_theory NONE NONE) I
(* TO BE DONE  merge the two commands together *)
*}
(*>*)


end

