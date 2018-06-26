(******************************************************************************
 * Citadelle
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

theory Aux_text
imports Main
  keywords "lazy_text" :: thy_decl
       and "reset_text" :: thy_decl
       and "apply_text" :: thy_decl
begin

ML\<open>
datatype code_printing = Code_printing of string

structure Data_code = Theory_Data
  (type T = code_printing list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_empty = ""

val _ =
  Outer_Syntax.command
    @{command_keyword lazy_text} ""
    (Parse.opt_target -- Parse.document_source
     >> (fn (_, code) =>
       let val _ = writeln (@{make_string} code) in
            Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn l => Code_printing (Input.source_content code) :: l)))
       end))

fun of_text s =
  let val s = String.substring (s, 2, String.size s - 4)
      val langle = "\<langle>"
      val rangle = "\<rangle>" in
  String.concat
    [ "txt'' [ " ^ langle ^ "\<open>", str #"\n", "  ", s, "\<close>" ^ rangle ^ " ]", str #"\n" ]
  end

fun apply_code_printing thy =
  (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
  |> (fn l =>
    let val (thy, l) =
      fold (fn Code_printing s => fn (thy, l) => (thy, of_text s :: l)) l (thy, [])
      ; val _ = writeln (Active.sendback_markup_command ("definition \<open>t txt'' = [\n              " ^ String.concatWith "            , " (rev l) ^ "]\<close>")) in
    thy
    end)

val () =
  Outer_Syntax.command @{command_keyword apply_text} ""
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory apply_code_printing))

val () =
  Outer_Syntax.command @{command_keyword reset_text} ""
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn _ => [])))))
\<close>

section\<open>Design\<close>

lazy_text\<open>\label{ex:employee-design:uml}\<close>
lazy_text\<open>
  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model.\<close>
lazy_text\<open>Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL.\<close>
lazy_text\<open>We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see \autoref{fig:person}):\<close>
lazy_text\<open>
\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person}}
\end{figure}
\<close>
lazy_text\<open>This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
\<close>
lazy_text\<open>Ideally, the following is generated automatically from a UML class model.\<close>
lazy_text\<open>Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows:\<close>
lazy_text\<open>Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables.\<close>
lazy_text\<open>Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL.\<close>
lazy_text\<open>Just a little check:\<close>
lazy_text\<open>To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.\<close>
lazy_text\<open>We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"}\<close>
lazy_text\<open>For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close>
lazy_text\<open>Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close>
lazy_text\<open>To denote OCL-types occurring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''\<close>
lazy_text\<open>\label{sec:edm-accessors}\<close>
lazy_text\<open>Should be generated entirely from a class-diagram.\<close>
lazy_text\<open>pointer undefined in state or not referencing a type conform object representation\<close>
lazy_text\<open>
The example we are defining in this section comes from the figure~\ref{fig:edm1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:edm1_system-states}
\end{figure}
\<close>

apply_text () reset_text ()

section\<open>Analysis\<close>

lazy_text\<open>\label{ex:employee-analysis:uml}\<close>
lazy_text\<open>
  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model.\<close>
lazy_text\<open>Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL.\<close>
lazy_text\<open>We are presenting here an ``analysis-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model'' (see \autoref{ex:employee-design:uml}).
To be precise, this theory contains the formalization of the data-part
covered by the UML class model (see \autoref{fig:person-ana}):\<close>
lazy_text\<open>
\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person-ana}}
\end{figure}
\<close>
lazy_text\<open>This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
\<close>
lazy_text\<open>Ideally, the following is generated automatically from a UML class model.\<close>
lazy_text\<open>Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows:\<close>
lazy_text\<open>Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables.\<close>
lazy_text\<open>Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL.\<close>
lazy_text\<open>To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.\<close>
lazy_text\<open>We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"}\<close>
lazy_text\<open>For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close>
lazy_text\<open>Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close>
lazy_text\<open>To denote OCL-types occurring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''\<close>
lazy_text\<open>\label{sec:eam-accessors}\<close>
lazy_text\<open>Should be generated entirely from a class-diagram.\<close>
lazy_text\<open>We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.''\<close>
lazy_text\<open>From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).\<close>
lazy_text\<open>The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}:\<close>
lazy_text\<open>pointer undefined in state or not referencing a type conform object representation\<close>
lazy_text\<open>
The example we are defining in this section comes from the figure~\ref{fig:eam1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:eam1_system-states}
\end{figure}
\<close>

apply_text () reset_text ()

end
