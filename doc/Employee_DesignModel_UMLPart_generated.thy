theory Employee_DesignModel_UMLPart_generated imports "../src/UML_Main"   "../src/compiler/Static"   "../src/compiler/Generator_dynamic_sequential" begin

(* 1 ************************************ 0 + 0 *)  (* term Floor1_infra.print_infra_enum_synonym *)

(* 2 ************************************ 0 + 1 *)
text \<open>
   \label{ex:Employee-DesignModel-UMLPart-generatedemployee-design:uml} \<close>

(* 3 ************************************ 1 + 1 *)
text \<open>\<close>

(* 4 ************************************ 2 + 1 *)
section \<open>Class Model: Introduction\<close>

(* 5 ************************************ 3 + 1 *)
text \<open>

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside \HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close>

(* 6 ************************************ 4 + 1 *)
text \<open>
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the \ML level.  This has been done, for a semantics
  following the open-world assumption, for \UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for \UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/\HOL. \<close>

(* 7 ************************************ 5 + 1 *)
subsection \<open>Outlining the Example\<close>

(* 8 ************************************ 6 + 1 *)
text \<open>
   We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the \OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the \UML class model (see \autoref{fig:Employee-DesignModel-UMLPart-generatedperson}):\<close>

(* 9 ************************************ 7 + 1 *)
text \<open>\<close>

(* 10 ************************************ 8 + 1 *)
text_raw \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple \UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:Employee-DesignModel-UMLPart-generatedperson}}
\end{figure}
\<close>

(* 11 ************************************ 9 + 1 *)
text_raw \<open>\<close>

(* 12 ************************************ 10 + 1 *)
text \<open>
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the \OCL part
captured by the subsequent theory).
\<close>

(* 13 ************************************ 11 + 1 *)
section \<open>Class Model: The Construction of the Object Universe\<close>

(* 14 ************************************ 12 + 1 *)
text \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close>

(* 15 ************************************ 13 + 8 *)  (* term Floor1_infra.print_infra_datatype_class_1 *)
datatype ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid" "nat option" "int option" "unit option" "bool option" "oid list list option"
datatype ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "oid list option" "int option"
datatype ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "oid" "unit option" "bool option" "oid list list option"
datatype ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t" "nat option" "int option"
datatype ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "oid"
datatype ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y" "unit option" "bool option" "oid list list option"
datatype ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid"
datatype ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 16 ************************************ 21 + 11 *)  (* term Floor1_infra.print_infra_datatype_class_2 *)
datatype ty2\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid list option" "int option"
datatype ty2oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk2oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid" "nat option" "int option" "unit option" "bool option" "oid list list option" "ty2\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
datatype ty2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty2\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
datatype ty2\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "nat option" "int option" "ty2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option"
datatype ty2oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk2oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "oid" "unit option" "bool option" "oid list list option" "ty2\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t"
datatype ty2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "ty2\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t"
datatype ty2\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "unit option" "bool option" "oid list list option" "ty2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option"
datatype ty2oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk2oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "oid" "ty2\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
datatype ty2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty2\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
datatype ty2\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option"
datatype ty2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid" "ty2\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 17 ************************************ 32 + 8 *)  (* term Floor1_infra.print_infra_datatype_equiv_2of1 *)
definition "class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = (\<lambda>oid inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d. (\<lambda> (mk2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y))))"
definition "class_ty_ext_equiv_2of1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = (\<lambda> (mk2oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)) \<Rightarrow> (class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)))"
definition "class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = (\<lambda>oid inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d. (\<lambda> (mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (t)) \<Rightarrow> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((case t of None \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))
    | \<lfloor>(mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))\<rfloor> \<Rightarrow> (case (class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)) of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y))))))) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t))))"
definition "class_ty_ext_equiv_2of1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = (\<lambda> (mk2oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)) \<Rightarrow> (class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)))"
definition "class_ty_ext_equiv_2of1_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = (\<lambda>oid. (\<lambda> (mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)) \<Rightarrow> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((case t of None \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid))
    | \<lfloor>(mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t))\<rfloor> \<Rightarrow> (case (class_ty_ext_equiv_2of1_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (t)) of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t))))
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))))) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))))"
definition "class_ty_ext_equiv_2of1\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = (\<lambda> (mk2oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid) (t)) \<Rightarrow> (class_ty_ext_equiv_2of1_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid) (t)))"
definition "class_ty_ext_equiv_2of1_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda>oid. (\<lambda> (mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((case t of None \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid))
    | \<lfloor>(mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t))\<rfloor> \<Rightarrow> (case (class_ty_ext_equiv_2of1_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid) (t)) of (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid))) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid))) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))))
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t))) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t))))))))"
definition "class_ty_ext_equiv_2of1\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) (t)) \<Rightarrow> (class_ty_ext_equiv_2of1_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) (t)))"

(* 18 ************************************ 40 + 12 *)  (* term Floor1_infra.print_infra_datatype_equiv_1of2 *)
definition "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = (\<lambda> (mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (oid , inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))"
definition "class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (mk2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)))"
definition "class_ty_ext_equiv_1of2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) of (oid , inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (mk2oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid) (inh\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (inh\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (own\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (own\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y))))))))"
definition "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = (\<lambda> (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (oid , inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)
    | (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (oid , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)))"
definition "class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) ((case t of (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> None
    | (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> \<lfloor>(mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt))))\<rfloor>)))))"
definition "class_ty_ext_equiv_1of2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) of (oid , inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (mk2oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid) (inh\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (inh\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (inh\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (own\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (own\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t))))))))"
definition "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = (\<lambda> (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid)) \<Rightarrow> (oid)
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (oid))
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) of (oid , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (oid)))"
definition "class_ty_ext_equiv_1of2_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = (\<lambda> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) ((case t of (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid)) \<Rightarrow> None
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> \<lfloor>(mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (\<lfloor>(mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt))))\<rfloor>))))\<rfloor>)
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t))) of (oid , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> \<lfloor>(mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (tt))))\<rfloor>)))))"
definition "class_ty_ext_equiv_1of2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = (\<lambda> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) of (oid) \<Rightarrow> (mk2oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (oid) ((class_ty_ext_equiv_1of2_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t) (own\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (own\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (own\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d))))))))"
definition "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid)) \<Rightarrow> (oid)
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (oid))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) of (oid , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> (oid))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t) (var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)))) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) of (oid) \<Rightarrow> (oid)))"
definition "class_ty_ext_equiv_1of2_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> (mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((case t of (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid)) \<Rightarrow> None
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (var\<^sub>b\<^sub>o\<^sub>s\<^sub>s) (var\<^sub>s\<^sub>a\<^sub>l\<^sub>a\<^sub>r\<^sub>y)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t))) of (oid , var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e , var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> \<lfloor>(mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (\<lfloor>(mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t) (\<lfloor>(mk2\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (tt))))\<rfloor>))))\<rfloor>))))\<rfloor>)
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (var\<^sub>w\<^sub>o\<^sub>r\<^sub>m\<^sub>h\<^sub>o\<^sub>l\<^sub>e) (var\<^sub>w\<^sub>e\<^sub>i\<^sub>g\<^sub>h\<^sub>t)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t))) of (oid , var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d , var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g , var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) \<Rightarrow> \<lfloor>(mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d) (\<lfloor>(mk2\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((class_ty_ext_equiv_1of2_aux\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (tt))))\<rfloor>))))\<rfloor>)
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (tt)) \<Rightarrow> (case (case tt of (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t) (var\<^sub>s\<^sub>o\<^sub>u\<^sub>n\<^sub>d) (var\<^sub>m\<^sub>o\<^sub>v\<^sub>i\<^sub>n\<^sub>g) (var\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>w\<^sub>o\<^sub>r\<^sub>l\<^sub>d)) \<Rightarrow> (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t))) of (oid) \<Rightarrow> \<lfloor>(mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((class_ty_ext_equiv_1of2_aux\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (tt))))\<rfloor>)))))"
definition "class_ty_ext_equiv_1of2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) of (oid) \<Rightarrow> (mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) ((class_ty_ext_equiv_1of2_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t))))))))"

(* 19 ************************************ 52 + 1 *)
text \<open>
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. \<close>

(* 20 ************************************ 53 + 1 *)  (* term Floor1_infra.print_infra_datatype_universe *)
datatype \<AA> = in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t"
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 21 ************************************ 54 + 1 *)
text \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to \OCL types. Again, we exploit that our representation of \OCL is a ``shallow embedding'' with a
one-to-one correspondance of \OCL-types to types of the meta-language \HOL. \<close>

(* 22 ************************************ 55 + 7 *)  (* term Floor1_infra.print_infra_type_synonym_class *)
type_synonym Void = "\<AA> Void"
type_synonym Boolean = "\<AA> Boolean"
type_synonym Integer = "\<AA> Integer"
type_synonym Real = "\<AA> Real"
type_synonym String = "\<AA> String"
type_synonym '\<alpha> val' = "(\<AA>, '\<alpha>) val"
type_notation val' ("\<cdot>(_)")

(* 23 ************************************ 62 + 4 *)  (* term Floor1_infra.print_infra_type_synonym_class_higher *)
type_synonym Person = "\<langle>\<langle>ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Planet = "\<langle>\<langle>ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Galaxy = "\<langle>\<langle>ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym OclAny = "\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"

(* 24 ************************************ 66 + 3 *)  (* term Floor1_infra.print_infra_type_synonym_class_rec *)
type_synonym Sequence_Person = "(\<AA>, ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Person = "(\<AA>, ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Sequence_Planet = "(\<AA>, ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

(* 25 ************************************ 69 + 0 *)  (* term Floor1_infra.print_infra_enum_syn *)

(* 26 ************************************ 69 + 1 *)
text \<open>
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the Object ID (oid) of the object. \<close>

(* 27 ************************************ 70 + 4 *)  (* term Floor1_infra.print_infra_instantiation_class *)
instantiation ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: object
begin
  definition oid_of_ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def : "oid_of = (\<lambda> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n t _ _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (_) (_) (_) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: object
begin
  definition oid_of_ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def : "oid_of = (\<lambda> mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t t _ _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (_) (_) (_)) \<Rightarrow> t
    | (mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: object
begin
  definition oid_of_ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_def : "oid_of = (\<lambda> mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y t _ _ _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> t
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 28 ************************************ 74 + 1 *)  (* term Floor1_infra.print_infra_instantiation_universe *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n Person \<Rightarrow> oid_of Person
    | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t Planet \<Rightarrow> oid_of Planet
    | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y Galaxy \<Rightarrow> oid_of Galaxy
    | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 29 ************************************ 75 + 1 *)
section \<open>Class Model: Instantiation of the Generic Strict Equality\<close>

(* 30 ************************************ 76 + 1 *)
text \<open>
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"} \<close>

(* 31 ************************************ 77 + 4 *)  (* term Floor1_infra.print_instantia_def_strictrefeq *)
overloading StrictRefEq \<equiv> "(StrictRefEq::(\<cdot>Person) \<Rightarrow> _ \<Rightarrow> _)"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "(x::\<cdot>Person) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end
overloading StrictRefEq \<equiv> "(StrictRefEq::(\<cdot>Planet) \<Rightarrow> _ \<Rightarrow> _)"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "(x::\<cdot>Planet) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end
overloading StrictRefEq \<equiv> "(StrictRefEq::(\<cdot>Galaxy) \<Rightarrow> _ \<Rightarrow> _)"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "(x::\<cdot>Galaxy) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end
overloading StrictRefEq \<equiv> "(StrictRefEq::(\<cdot>OclAny) \<Rightarrow> _ \<Rightarrow> _)"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::\<cdot>OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end

(* 32 ************************************ 81 + 1 *)  (* term Floor1_infra.print_instantia_lemmas_strictrefeq *)
lemmas[simp,code_unfold] = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 33 ************************************ 82 + 1 *)
text \<open>
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close>

(* 34 ************************************ 83 + 1 *)
text \<open>
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close>

(* 35 ************************************ 84 + 1 *)
section \<open>Class Model: OclAsType\<close>

(* 36 ************************************ 85 + 1 *)
subsection \<open>Definition\<close>

(* 37 ************************************ 86 + 4 *)  (* term Floor1_astype.print_astype_consts *)
consts OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> \<cdot>Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> \<cdot>Planet" ("(_) .oclAsType'(Planet')")
consts OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> \<cdot>Galaxy" ("(_) .oclAsType'(Galaxy')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> \<cdot>OclAny" ("(_) .oclAsType'(OclAny')")

(* 38 ************************************ 90 + 16 *)  (* term Floor1_astype.print_astype_class *)
overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::\<cdot>Person) .oclAsType(Person) \<equiv> x"
end
overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::\<cdot>Planet) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::\<cdot>Galaxy) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::\<cdot>OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::\<cdot>Planet) .oclAsType(Planet) \<equiv> x"
end
overloading OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::\<cdot>Galaxy) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::\<cdot>Person) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
end
overloading OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclAsType(Galaxy) \<equiv> x"
end
overloading OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
end
overloading OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::\<cdot>Person) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None) (None))\<rfloor>\<rfloor>))"
end
overloading OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::\<cdot>Planet) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None) (None))\<rfloor>\<rfloor>))"
end
overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclAsType(OclAny) \<equiv> x"
end
overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::\<cdot>Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor>))"
end
overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::\<cdot>Planet) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor>))"
end
overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor>))"
end

(* 39 ************************************ 106 + 4 *)  (* term Floor1_astype.print_astype_from_universe *)
definition "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)))))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_) (_)))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)))))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None) (None))\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = Some o (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))"

(* 40 ************************************ 110 + 1 *)  (* term Floor1_astype.print_astype_lemmas_id *)
lemmas[simp,code_unfold] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 41 ************************************ 111 + 1 *)
subsection \<open>Context Passing\<close>

(* 42 ************************************ 112 + 64 *)  (* term Floor1_astype.print_astype_lemma_cp *)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclAsType(Person)))))"
by(rule cpI1, simp)

(* 43 ************************************ 176 + 1 *)  (* term Floor1_astype.print_astype_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                            cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                            cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                            cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 44 ************************************ 177 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 45 ************************************ 178 + 32 *)  (* term Floor1_astype.print_astype_lemma_strict *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::\<cdot>Person) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclAsType(Galaxy)) = invalid"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclAsType(Galaxy)) = null"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::\<cdot>Person) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::\<cdot>Planet) .oclAsType(Planet)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::\<cdot>Person) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::\<cdot>Galaxy) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::\<cdot>Planet) .oclAsType(Planet)) = null"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::\<cdot>Person) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::\<cdot>Planet) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::\<cdot>Person) .oclAsType(Person)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::\<cdot>Galaxy) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::\<cdot>Planet) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::\<cdot>Person) .oclAsType(Person)) = null"
by(simp)

(* 46 ************************************ 210 + 1 *)  (* term Floor1_astype.print_astype_lemmas_strict *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 47 ************************************ 211 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 48 ************************************ 212 + 6 *)  (* term Floor1_astype.print_astype_defined *)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclAsType(Planet)))"
  using isdef
by(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy foundation16 null_option_def bot_option_def)

(* 49 ************************************ 218 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 50 ************************************ 219 + 6 *)  (* term Floor1_astype.print_astype_up_d_cast0 *)
lemma up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Person) .oclAsType(Planet)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Person) .oclAsType(Galaxy)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Person) .oclAsType(OclAny)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Planet) .oclAsType(Galaxy)) .oclAsType(Planet)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Planet) .oclAsType(OclAny)) .oclAsType(Planet)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast0 :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Galaxy) .oclAsType(OclAny)) .oclAsType(Galaxy)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)

(* 51 ************************************ 225 + 6 *)  (* term Floor1_astype.print_astype_up_d_cast *)
lemma up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast :
shows "(((X::\<cdot>Person) .oclAsType(Planet)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast :
shows "(((X::\<cdot>Person) .oclAsType(Galaxy)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast :
shows "(((X::\<cdot>Person) .oclAsType(OclAny)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast :
shows "(((X::\<cdot>Planet) .oclAsType(Galaxy)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast :
shows "(((X::\<cdot>Planet) .oclAsType(OclAny)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast :
shows "(((X::\<cdot>Galaxy) .oclAsType(OclAny)) .oclAsType(Galaxy)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done

(* 52 ************************************ 231 + 6 *)  (* term Floor1_astype.print_astype_d_up_cast *)
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast :
assumes def_X: "X = ((Y::\<cdot>Person) .oclAsType(Planet))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(Planet)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast :
assumes def_X: "X = ((Y::\<cdot>Person) .oclAsType(Galaxy))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(Galaxy)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast :
assumes def_X: "X = ((Y::\<cdot>Person) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)
lemma down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast :
assumes def_X: "X = ((Y::\<cdot>Planet) .oclAsType(Galaxy))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Planet)) .oclAsType(Galaxy)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)
lemma down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast :
assumes def_X: "X = ((Y::\<cdot>Planet) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Planet)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)
lemma down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast :
assumes def_X: "X = ((Y::\<cdot>Galaxy) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Galaxy)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym)

(* 53 ************************************ 237 + 1 *)
subsection \<open>Const\<close>

(* 54 ************************************ 238 + 16 *)  (* term Floor1_astype.print_astype_lemma_const *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_const : "(const ((X::\<cdot>OclAny))) \<Longrightarrow> (const (X .oclAsType(OclAny)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_const : "(const ((X::\<cdot>Galaxy))) \<Longrightarrow> (const (X .oclAsType(OclAny)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_const : "(const ((X::\<cdot>Planet))) \<Longrightarrow> (const (X .oclAsType(OclAny)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_const : "(const ((X::\<cdot>Person))) \<Longrightarrow> (const (X .oclAsType(OclAny)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_const : "(const ((X::\<cdot>OclAny))) \<Longrightarrow> (const (X .oclAsType(Galaxy)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_const : "(const ((X::\<cdot>Galaxy))) \<Longrightarrow> (const (X .oclAsType(Galaxy)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_const : "(const ((X::\<cdot>Planet))) \<Longrightarrow> (const (X .oclAsType(Galaxy)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_const : "(const ((X::\<cdot>Person))) \<Longrightarrow> (const (X .oclAsType(Galaxy)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_const : "(const ((X::\<cdot>OclAny))) \<Longrightarrow> (const (X .oclAsType(Planet)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_const : "(const ((X::\<cdot>Galaxy))) \<Longrightarrow> (const (X .oclAsType(Planet)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_const : "(const ((X::\<cdot>Planet))) \<Longrightarrow> (const (X .oclAsType(Planet)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_const : "(const ((X::\<cdot>Person))) \<Longrightarrow> (const (X .oclAsType(Planet)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_const : "(const ((X::\<cdot>OclAny))) \<Longrightarrow> (const (X .oclAsType(Person)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_const : "(const ((X::\<cdot>Galaxy))) \<Longrightarrow> (const (X .oclAsType(Person)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_const : "(const ((X::\<cdot>Planet))) \<Longrightarrow> (const (X .oclAsType(Person)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_const : "(const ((X::\<cdot>Person))) \<Longrightarrow> (const (X .oclAsType(Person)))"
by(simp add: const_def, (metis (no_types) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person prod.collapse bot_option_def invalid_def null_fun_def null_option_def)?)

(* 55 ************************************ 254 + 1 *)  (* term Floor1_astype.print_astype_lemmas_const *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_const
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_const
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_const
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_const
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_const
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_const
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_const
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_const
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_const
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_const
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_const
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_const
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_const
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_const
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_const
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_const

(* 56 ************************************ 255 + 1 *)
section \<open>Class Model: OclIsTypeOf\<close>

(* 57 ************************************ 256 + 1 *)
subsection \<open>Definition\<close>

(* 58 ************************************ 257 + 4 *)  (* term Floor1_istypeof.print_istypeof_consts *)
consts OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Planet')")
consts OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Galaxy')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 59 ************************************ 261 + 16 *)  (* term Floor1_istypeof.print_istypeof_class *)
overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::\<cdot>Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::\<cdot>Planet) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::\<cdot>Galaxy) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::\<cdot>Planet) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::\<cdot>Galaxy) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::\<cdot>Person) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::\<cdot>Person) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::\<cdot>Planet) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::\<cdot>Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::\<cdot>Planet) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end
overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
end

(* 60 ************************************ 277 + 4 *)  (* term Floor1_istypeof.print_istypeof_from_universe *)
definition "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsTypeOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsTypeOf(Person))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Person)))"
definition "OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsTypeOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsTypeOf(Planet))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsTypeOf(Planet)))"
definition "OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsTypeOf(Galaxy))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsTypeOf(Galaxy)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsTypeOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))"

(* 61 ************************************ 281 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_id *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 62 ************************************ 282 + 1 *)
subsection \<open>Context Passing\<close>

(* 63 ************************************ 283 + 64 *)  (* term Floor1_istypeof.print_istypeof_lemma_cp *)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)

(* 64 ************************************ 347 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                            cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                            cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 65 ************************************ 348 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 66 ************************************ 349 + 32 *)  (* term Floor1_istypeof.print_istypeof_lemma_strict *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::\<cdot>Person) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::\<cdot>Person) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::\<cdot>Person) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::\<cdot>Planet) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::\<cdot>Person) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::\<cdot>Person) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::\<cdot>Planet) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::\<cdot>Person) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 67 ************************************ 381 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_strict *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                            OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 68 ************************************ 382 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 69 ************************************ 383 + 16 *)  (* term Floor1_istypeof.print_istypeof_defined *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy split: option.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy split: option.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy split: option.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy split: option.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)

(* 70 ************************************ 399 + 16 *)  (* term Floor1_istypeof.print_istypeof_defined' *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])

(* 71 ************************************ 415 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 72 ************************************ 416 + 6 *)  (* term Floor1_istypeof.print_istypeof_up_larger *)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsTypeOf(Planet)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsTypeOf(Galaxy)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsTypeOf(Galaxy)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy foundation22 foundation16 null_option_def bot_option_def)

(* 73 ************************************ 422 + 10 *)  (* term Floor1_istypeof.print_istypeof_up_d_cast *)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Planet_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclValid_def false_def true_def)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Planet :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy :
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)

(* 74 ************************************ 432 + 1 *)
subsection \<open>Const\<close>

(* 75 ************************************ 433 + 1 *)
section \<open>Class Model: OclIsKindOf\<close>

(* 76 ************************************ 434 + 1 *)
subsection \<open>Definition\<close>

(* 77 ************************************ 435 + 4 *)  (* term Floor1_iskindof.print_iskindof_consts *)
consts OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Planet')")
consts OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Galaxy')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 78 ************************************ 439 + 16 *)  (* term Floor1_iskindof.print_iskindof_class *)
overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::\<cdot>Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::\<cdot>Planet) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::\<cdot>Galaxy) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "(OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::\<cdot>Planet) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::\<cdot>Galaxy) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
end
overloading OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t \<equiv> "(OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::\<cdot>Person) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
end
overloading OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
end
overloading OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
end
overloading OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::\<cdot>Person) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
end
overloading OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y \<equiv> "(OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::\<cdot>Planet) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
end
overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
end
overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::\<cdot>Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
end
overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::\<cdot>Planet) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
end
overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::\<cdot>Galaxy) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
end

(* 79 ************************************ 455 + 4 *)  (* term Floor1_iskindof.print_iskindof_from_universe *)
definition "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsKindOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsKindOf(Person))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Person)))"
definition "OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsKindOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsKindOf(Planet))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsKindOf(Planet)))"
definition "OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsKindOf(Galaxy))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsKindOf(Galaxy)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::\<cdot>Person) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::\<cdot>Planet) .oclIsKindOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::\<cdot>Galaxy) .oclIsKindOf(OclAny)))"

(* 80 ************************************ 459 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_id *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 81 ************************************ 460 + 1 *)
subsection \<open>Context Passing\<close>

(* 82 ************************************ 461 + 64 *)  (* term Floor1_iskindof.print_iskindof_lemma_cp *)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Person)))::\<cdot>Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Planet)))::\<cdot>Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Galaxy)))::\<cdot>Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)

(* 83 ************************************ 525 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                            cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                            cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 84 ************************************ 526 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 85 ************************************ 527 + 32 *)  (* term Floor1_iskindof.print_iskindof_lemma_strict *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::\<cdot>Person) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::\<cdot>Person) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::\<cdot>Planet) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::\<cdot>Planet) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::\<cdot>Person) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::\<cdot>Person) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::\<cdot>Person) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::\<cdot>Person) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::\<cdot>Person) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::\<cdot>Planet) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::\<cdot>Planet) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::\<cdot>Galaxy) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::\<cdot>Galaxy) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null, simp)

(* 86 ************************************ 559 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_strict *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                            OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 87 ************************************ 560 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 88 ************************************ 561 + 16 *)  (* term Floor1_iskindof.print_iskindof_defined *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef]])

(* 89 ************************************ 577 + 16 *)  (* term Floor1_iskindof.print_iskindof_defined' *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])

(* 90 ************************************ 593 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 91 ************************************ 594 + 4 *)  (* term Floor1_iskindof.print_iskindof_up_eq_asty *)
lemma actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsKindOf(Person))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?)
lemma actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(Planet))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?)
lemma actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Galaxy))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy split: option.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?)
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny, subst (3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split ty\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?)

(* 92 ************************************ 598 + 6 *)  (* term Floor1_iskindof.print_iskindof_up_larger *)
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsKindOf(Planet))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
by(rule foundation25', rule actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[OF isdef])
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef])
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Person) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef])
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
by(rule foundation25', rule actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef])
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef])
lemma actualKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
by(rule foundation25', rule actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef])

(* 93 ************************************ 604 + 6 *)  (* term Floor1_iskindof.print_iskindof_up_istypeof_unfold *)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet)))"
shows "((\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Planet))) \<or> (\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Person))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others_unfold[OF isdef], blast)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Planet)))"
shows "((\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet))) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Person))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
done
lemma not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others_unfold :
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy)))"
shows "((\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy))) \<or> ((\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Person))) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet)))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
done

(* 94 ************************************ 610 + 6 *)  (* term Floor1_iskindof.print_iskindof_up_istypeof *)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsTypeOf(Planet))"
  using actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Planet)))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Planet))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsTypeOf(Galaxy))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Galaxy)))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done
lemma not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done

(* 95 ************************************ 616 + 10 *)  (* term Floor1_iskindof.print_iskindof_up_d_cast *)
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_Planet_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Planet) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Planet_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_Galaxy_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_OclAny_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Planet :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Planet, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Planet :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Galaxy :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet :
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
done

(* 96 ************************************ 626 + 1 *)
subsection \<open>Const\<close>

(* 97 ************************************ 627 + 1 *)
section \<open>Class Model: OclAllInstances\<close>

(* 98 ************************************ 628 + 1 *)
text \<open>
   To denote \OCL-types occurring in \OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.'' \<close>

(* 99 ************************************ 629 + 4 *)  (* term Floor1_allinst.print_allinst_def_id *)
definition "Person = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>"
definition "Planet = OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>"
definition "Galaxy = OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>"
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 100 ************************************ 633 + 1 *)  (* term Floor1_allinst.print_allinst_lemmas_id *)
lemmas[simp,code_unfold] = Person_def
                            Planet_def
                            Galaxy_def
                            OclAny_def

(* 101 ************************************ 634 + 1 *)  (* term Floor1_allinst.print_allinst_astype *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some : "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> (x)) \<noteq> None"
by(simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

(* 102 ************************************ 635 + 3 *)  (* term Floor1_allinst.print_allinst_exec *)
lemma OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_generic (pre_post) (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((pre_post (\<tau>))))))\<rfloor>\<rfloor>)))"
  proof - let ?S1 = "(\<lambda>\<tau>. OclAny ` (ran ((heap ((pre_post (\<tau>)))))))" show ?thesis
  proof - let ?S2 = "(\<lambda>\<tau>. ((?S1) (\<tau>)) - {None})" show ?thesis
  proof - have B: "(\<And>\<tau>. ((?S2) (\<tau>)) \<subseteq> ((?S1) (\<tau>)))" by(auto) show ?thesis
  proof - have C: "(\<And>\<tau>. ((?S1) (\<tau>)) \<subseteq> ((?S2) (\<tau>)))" by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some) show ?thesis
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
by(insert equalityI[OF B, OF C], simp) qed qed qed qed
lemma OclAllInstances_at_post\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_at_post (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((snd (\<tau>))))))\<rfloor>\<rfloor>)))"
  unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec)
lemma OclAllInstances_at_pre\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_at_pre (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((fst (\<tau>))))))\<rfloor>\<rfloor>)))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec)

(* 103 ************************************ 638 + 1 *)
subsection \<open>OclIsTypeOf\<close>

(* 104 ************************************ 639 + 2 *)  (* term Floor1_allinst.print_allinst_istypeof_pre *)
lemma ex_ssubst : "(\<forall>x \<in> B. (s (x)) = (t (x))) \<Longrightarrow> (\<exists>x \<in> B. (P ((s (x))))) = (\<exists>x \<in> B. (P ((t (x)))))"
by(simp)
lemma ex_def : "x \<in> \<lceil>\<lceil>\<lfloor>\<lfloor>Some ` (X - {None})\<rfloor>\<rfloor>\<rceil>\<rceil> \<Longrightarrow> (\<exists>y. x = \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)"
by(auto)

(* 105 ************************************ 641 + 21 *)  (* term Floor1_allinst.print_allinst_istypeof *)
lemma Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Person)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[simplified OclValid_def, simplified OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
lemma Person_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
lemma Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1, simp)
lemma Planet_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1, simp)
lemma Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (a))) (None) (None))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma Planet_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2, simp)
lemma Planet_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2, simp)
lemma Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp)
lemma Galaxy_OclAllInstances_at_post_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1, simp)
lemma Galaxy_OclAllInstances_at_pre_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1, simp)
lemma Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (a))) (None) (None) (None))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma Galaxy_OclAllInstances_at_post_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2, simp)
lemma Galaxy_OclAllInstances_at_pre_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2, simp)
lemma OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp)
lemma OclAny_OclAllInstances_at_post_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp)
lemma OclAny_OclAllInstances_at_pre_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp)
lemma OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 :
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (a))))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma OclAny_OclAllInstances_at_post_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp)
lemma OclAny_OclAllInstances_at_pre_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 :
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp)

(* 106 ************************************ 662 + 1 *)
subsection \<open>OclIsKindOf\<close>

(* 107 ************************************ 663 + 12 *)  (* term Floor1_allinst.print_allinst_iskindof_eq *)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Person)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Planet)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)
lemma Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Galaxy_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma Galaxy_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma OclAny_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma OclAny_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

(* 108 ************************************ 675 + 18 *)  (* term Floor1_allinst.print_allinst_iskindof_larger *)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Planet)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Galaxy_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)
lemma Galaxy_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

(* 109 ************************************ 693 + 1 *)
section \<open>Class Model: The Accessors\<close>

(* 110 ************************************ 694 + 1 *)
text \<open>
  \label{sec:Employee-DesignModel-UMLPart-generatededm-accessors}\<close>

(* 111 ************************************ 695 + 1 *)
text \<open>\<close>

(* 112 ************************************ 696 + 1 *)
subsection \<open>Definition\<close>

(* 113 ************************************ 697 + 1 *)
text \<open>\<close>

(* 114 ************************************ 698 + 1 *)  (* term Floor1_access.print_access_oid_uniq_ml *)
ML \<open>val oidPerson_0_boss = 0\<close>

(* 115 ************************************ 699 + 1 *)  (* term Floor1_access.print_access_oid_uniq *)
definition "oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss = 0"

(* 116 ************************************ 700 + 1 *)
text \<open>\<close>

(* 117 ************************************ 701 + 5 *)  (* term Floor1_access.print_access_eval_extract *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)"
definition "reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e o (reconst_basetype (x))"

(* 118 ************************************ 706 + 1 *)
text \<open>\<close>

(* 119 ************************************ 707 + 2 *)  (* term Floor1_access.print_access_choose_ml *)
ML \<open>val switch2_01 = (fn [x0 , x1] => (x0 , x1))\<close>
ML \<open>val switch2_10 = (fn [x0 , x1] => (x1 , x0))\<close>

(* 120 ************************************ 709 + 3 *)  (* term Floor1_access.print_access_choose *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"
definition "deref_assocs pre_post to_from assoc_oid f oid = (\<lambda>\<tau>. (case (assocs ((pre_post (\<tau>))) (assoc_oid)) of \<lfloor>S\<rfloor> \<Rightarrow> (f ((deref_assocs_list (to_from) (oid) (S))) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"

(* 121 ************************************ 712 + 4 *)  (* term Floor1_access.print_access_deref_oid *)
definition "deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 122 ************************************ 716 + 0 *)  (* term Floor1_access.print_access_deref_assocs *)

(* 123 ************************************ 716 + 1 *)
text \<open>
   pointer undefined in state or not referencing a type conform object representation \<close>

(* 124 ************************************ 717 + 15 *)  (* term Floor1_access.print_access_select *)
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>x___boss\<rfloor>) (_)) \<Rightarrow> (f (x___boss)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>x___salary\<rfloor>)) \<Rightarrow> (f (x___salary)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole f = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>x___wormhole\<rfloor>) (_)) \<Rightarrow> (f (x___wormhole)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight f = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>x___weight\<rfloor>)) \<Rightarrow> (f (x___weight)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound f = (\<lambda> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<bottom>) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<lfloor>x___sound\<rfloor>) (_) (_)) \<Rightarrow> (f (x___sound)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving f = (\<lambda> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<lfloor>x___moving\<rfloor>) (_)) \<Rightarrow> (f (x___moving)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world f = (\<lambda> (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (_) (\<lfloor>x___outer_world\<rfloor>)) \<Rightarrow> (f (x___outer_world)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_) (_) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>x___wormhole\<rfloor>) (_) (_) (_) (_))) (_) (_)) \<Rightarrow> (f (x___wormhole)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>) (_) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>x___weight\<rfloor>) (_) (_) (_))) (_) (_)) \<Rightarrow> (f (x___weight)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<lfloor>x___sound\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f (x___sound)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (\<lfloor>x___moving\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f (x___moving)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world f = (\<lambda> (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (_) (\<lfloor>x___outer_world\<rfloor>))) (_) (_)) \<Rightarrow> (f (x___outer_world)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound f = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>x___sound\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f (x___sound))
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound (f) (person)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving f = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>x___moving\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f (x___moving))
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving (f) (person)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world f = (\<lambda> (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_) (\<lfloor>x___outer_world\<rfloor>))) (_) (_)) \<Rightarrow> (f (x___outer_world))
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world (f) (person)))"

(* 125 ************************************ 732 + 0 *)  (* term Floor1_access.print_access_select_obj *)

(* 126 ************************************ 732 + 14 *)  (* term Floor1_access.print_access_dot_consts *)
consts dot_0___boss :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Person" ("(_) .boss")
consts dot_0___bossat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Person" ("(_) .boss@pre")
consts dot__salary :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .salary")
consts dot__salaryat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .salary@pre")
consts dot__wormhole :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, nat option option) val" ("(_) .wormhole")
consts dot__wormholeat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, nat option option) val" ("(_) .wormhole@pre")
consts dot__weight :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .weight")
consts dot__weightat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .weight@pre")
consts dot__sound :: "(\<AA>, '\<alpha>) val \<Rightarrow> Void" ("(_) .sound")
consts dot__soundat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Void" ("(_) .sound@pre")
consts dot__moving :: "(\<AA>, '\<alpha>) val \<Rightarrow> Boolean" ("(_) .moving")
consts dot__movingat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Boolean" ("(_) .moving@pre")
consts dot__outer_world :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Sequence_Planet" ("(_) .outer'_world")
consts dot__outer_worldat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Sequence_Planet" ("(_) .outer'_world@pre")

(* 127 ************************************ 746 + 30 *)  (* term Floor1_access.print_access_dot *)
overloading dot_0___boss \<equiv> "(dot_0___boss::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss : "(x::\<cdot>Person) .boss \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss ((select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) (reconst_basetype))))))))))"
end
overloading dot__salary \<equiv> "(dot__salary::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary : "(x::\<cdot>Person) .salary \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary (reconst_basetype))))))"
end
overloading dot_0___bossat_pre \<equiv> "(dot_0___bossat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre : "(x::\<cdot>Person) .boss@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss ((select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) (reconst_basetype))))))))))"
end
overloading dot__salaryat_pre \<equiv> "(dot__salaryat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre : "(x::\<cdot>Person) .salary@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary (reconst_basetype))))))"
end
overloading dot__wormhole \<equiv> "(dot__wormhole::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole : "(x::\<cdot>Planet) .wormhole \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole (reconst_basetype))))))"
end
overloading dot__weight \<equiv> "(dot__weight::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight : "(x::\<cdot>Planet) .weight \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight (reconst_basetype))))))"
end
overloading dot__wormholeat_pre \<equiv> "(dot__wormholeat_pre::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre : "(x::\<cdot>Planet) .wormhole@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole (reconst_basetype))))))"
end
overloading dot__weightat_pre \<equiv> "(dot__weightat_pre::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre : "(x::\<cdot>Planet) .weight@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight (reconst_basetype))))))"
end
overloading dot__sound \<equiv> "(dot__sound::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound : "(x::\<cdot>Galaxy) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__moving \<equiv> "(dot__moving::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving : "(x::\<cdot>Galaxy) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving (reconst_basetype))))))"
end
overloading dot__outer_world \<equiv> "(dot__outer_world::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world : "(x::\<cdot>Galaxy) .outer_world \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) (reconst_basetype))))))))))))"
end
overloading dot__soundat_pre \<equiv> "(dot__soundat_pre::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre : "(x::\<cdot>Galaxy) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__movingat_pre \<equiv> "(dot__movingat_pre::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre : "(x::\<cdot>Galaxy) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving (reconst_basetype))))))"
end
overloading dot__outer_worldat_pre \<equiv> "(dot__outer_worldat_pre::(\<cdot>Galaxy) \<Rightarrow> _)"
begin
  definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre : "(x::\<cdot>Galaxy) .outer_world@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) (reconst_basetype))))))))))))"
end
overloading dot__wormhole \<equiv> "(dot__wormhole::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole : "(x::\<cdot>Person) .wormhole \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole (reconst_basetype))))))"
end
overloading dot__weight \<equiv> "(dot__weight::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight : "(x::\<cdot>Person) .weight \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight (reconst_basetype))))))"
end
overloading dot__sound \<equiv> "(dot__sound::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound : "(x::\<cdot>Person) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__moving \<equiv> "(dot__moving::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving : "(x::\<cdot>Person) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving (reconst_basetype))))))"
end
overloading dot__outer_world \<equiv> "(dot__outer_world::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world : "(x::\<cdot>Person) .outer_world \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) (reconst_basetype))))))))))))"
end
overloading dot__wormholeat_pre \<equiv> "(dot__wormholeat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre : "(x::\<cdot>Person) .wormhole@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole (reconst_basetype))))))"
end
overloading dot__weightat_pre \<equiv> "(dot__weightat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre : "(x::\<cdot>Person) .weight@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight (reconst_basetype))))))"
end
overloading dot__soundat_pre \<equiv> "(dot__soundat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre : "(x::\<cdot>Person) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__movingat_pre \<equiv> "(dot__movingat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre : "(x::\<cdot>Person) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving (reconst_basetype))))))"
end
overloading dot__outer_worldat_pre \<equiv> "(dot__outer_worldat_pre::(\<cdot>Person) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre : "(x::\<cdot>Person) .outer_world@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) (reconst_basetype))))))))))))"
end
overloading dot__sound \<equiv> "(dot__sound::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound : "(x::\<cdot>Planet) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__moving \<equiv> "(dot__moving::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving : "(x::\<cdot>Planet) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving (reconst_basetype))))))"
end
overloading dot__outer_world \<equiv> "(dot__outer_world::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world : "(x::\<cdot>Planet) .outer_world \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) (reconst_basetype))))))))))))"
end
overloading dot__soundat_pre \<equiv> "(dot__soundat_pre::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre : "(x::\<cdot>Planet) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound (reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d))))))"
end
overloading dot__movingat_pre \<equiv> "(dot__movingat_pre::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre : "(x::\<cdot>Planet) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving (reconst_basetype))))))"
end
overloading dot__outer_worldat_pre \<equiv> "(dot__outer_worldat_pre::(\<cdot>Planet) \<Rightarrow> _)"
begin
  definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre : "(x::\<cdot>Planet) .outer_world@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world ((select_object\<^sub>S\<^sub>e\<^sub>t ((select_object\<^sub>S\<^sub>e\<^sub>q ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) (reconst_basetype))))))))))))"
end

(* 128 ************************************ 776 + 1 *)  (* term Floor1_access.print_access_dot_lemmas_id *)
lemmas dot_accessor = dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre

(* 129 ************************************ 777 + 1 *)
subsection \<open>Context Passing\<close>

(* 130 ************************************ 778 + 1 *)  (* term Floor1_access.print_access_dot_cp_lemmas *)
lemmas[simp,code_unfold] = eval_extract_def

(* 131 ************************************ 779 + 30 *)  (* term Floor1_access.print_access_dot_lemma_cp *)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss : "(cp ((\<lambda>X. (X::\<cdot>Person) .boss)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary : "(cp ((\<lambda>X. (X::\<cdot>Person) .salary)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .boss@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .salary@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole : "(cp ((\<lambda>X. (X::\<cdot>Planet) .wormhole)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight : "(cp ((\<lambda>X. (X::\<cdot>Planet) .weight)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre : "(cp ((\<lambda>X. (X::\<cdot>Planet) .wormhole@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre : "(cp ((\<lambda>X. (X::\<cdot>Planet) .weight@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .outer_world)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .moving@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre : "(cp ((\<lambda>X. (X::\<cdot>Galaxy) .outer_world@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole : "(cp ((\<lambda>X. (X::\<cdot>Person) .wormhole)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight : "(cp ((\<lambda>X. (X::\<cdot>Person) .weight)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound : "(cp ((\<lambda>X. (X::\<cdot>Person) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving : "(cp ((\<lambda>X. (X::\<cdot>Person) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world : "(cp ((\<lambda>X. (X::\<cdot>Person) .outer_world)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .wormhole@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .weight@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .moving@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre : "(cp ((\<lambda>X. (X::\<cdot>Person) .outer_world@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound : "(cp ((\<lambda>X. (X::\<cdot>Planet) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving : "(cp ((\<lambda>X. (X::\<cdot>Planet) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world : "(cp ((\<lambda>X. (X::\<cdot>Planet) .outer_world)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre : "(cp ((\<lambda>X. (X::\<cdot>Planet) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre : "(cp ((\<lambda>X. (X::\<cdot>Planet) .moving@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre : "(cp ((\<lambda>X. (X::\<cdot>Planet) .outer_world@pre)))"
by(auto simp: dot_accessor cp_def)

(* 132 ************************************ 809 + 1 *)  (* term Floor1_access.print_access_dot_lemmas_cp *)
lemmas[simp,code_unfold] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre

(* 133 ************************************ 810 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 134 ************************************ 811 + 60 *)  (* term Floor1_access.print_access_lemma_strict *)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss_invalid : "(invalid::\<cdot>Person) .boss = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss_null : "(null::\<cdot>Person) .boss = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary_invalid : "(invalid::\<cdot>Person) .salary = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary_null : "(null::\<cdot>Person) .salary = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre_invalid : "(invalid::\<cdot>Person) .boss@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre_null : "(null::\<cdot>Person) .boss@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre_invalid : "(invalid::\<cdot>Person) .salary@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre_null : "(null::\<cdot>Person) .salary@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole_invalid : "(invalid::\<cdot>Planet) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole_null : "(null::\<cdot>Planet) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight_invalid : "(invalid::\<cdot>Planet) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight_null : "(null::\<cdot>Planet) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre_invalid : "(invalid::\<cdot>Planet) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre_null : "(null::\<cdot>Planet) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre_invalid : "(invalid::\<cdot>Planet) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre_null : "(null::\<cdot>Planet) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound_invalid : "(invalid::\<cdot>Galaxy) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound_null : "(null::\<cdot>Galaxy) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving_invalid : "(invalid::\<cdot>Galaxy) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving_null : "(null::\<cdot>Galaxy) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world_invalid : "(invalid::\<cdot>Galaxy) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world_null : "(null::\<cdot>Galaxy) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre_invalid : "(invalid::\<cdot>Galaxy) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre_null : "(null::\<cdot>Galaxy) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre_invalid : "(invalid::\<cdot>Galaxy) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre_null : "(null::\<cdot>Galaxy) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre_invalid : "(invalid::\<cdot>Galaxy) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre_null : "(null::\<cdot>Galaxy) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole_invalid : "(invalid::\<cdot>Person) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole_null : "(null::\<cdot>Person) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight_invalid : "(invalid::\<cdot>Person) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight_null : "(null::\<cdot>Person) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound_invalid : "(invalid::\<cdot>Person) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound_null : "(null::\<cdot>Person) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving_invalid : "(invalid::\<cdot>Person) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving_null : "(null::\<cdot>Person) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world_invalid : "(invalid::\<cdot>Person) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world_null : "(null::\<cdot>Person) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre_invalid : "(invalid::\<cdot>Person) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre_null : "(null::\<cdot>Person) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre_invalid : "(invalid::\<cdot>Person) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre_null : "(null::\<cdot>Person) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre_invalid : "(invalid::\<cdot>Person) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre_null : "(null::\<cdot>Person) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre_invalid : "(invalid::\<cdot>Person) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre_null : "(null::\<cdot>Person) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre_invalid : "(invalid::\<cdot>Person) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre_null : "(null::\<cdot>Person) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound_invalid : "(invalid::\<cdot>Planet) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound_null : "(null::\<cdot>Planet) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving_invalid : "(invalid::\<cdot>Planet) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving_null : "(null::\<cdot>Planet) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world_invalid : "(invalid::\<cdot>Planet) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world_null : "(null::\<cdot>Planet) .outer_world = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre_invalid : "(invalid::\<cdot>Planet) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre_null : "(null::\<cdot>Planet) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre_invalid : "(invalid::\<cdot>Planet) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre_null : "(null::\<cdot>Planet) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre_invalid : "(invalid::\<cdot>Planet) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre_null : "(null::\<cdot>Planet) .outer_world@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)

(* 135 ************************************ 871 + 1 *)
subsection \<open>Representation in States\<close>

(* 136 ************************************ 872 + 30 *)  (* term Floor1_access.print_access_def_mono *)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .boss)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .salary)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salary_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .boss@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .salary@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__salaryat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .wormhole)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormhole_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .weight)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weight_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .wormhole@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__wormholeat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .weight@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__weightat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__sound_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__moving_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .outer_world)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_world_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__soundat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__movingat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Galaxy) .outer_world@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y__outer_worldat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .wormhole)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormhole_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .weight)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weight_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__sound_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__moving_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .outer_world)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_world_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .wormhole@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__wormholeat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .weight@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__weightat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__soundat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__movingat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .outer_world@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__outer_worldat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__sound_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__moving_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .outer_world)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_world_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__soundat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__movingat_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Planet) .outer_world@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .outer_world@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t__outer_worldat_pre_null)
by(simp add: defined_split)

(* 137 ************************************ 902 + 2 *)  (* term Floor1_access.print_access_is_repr *)
lemma is_repr_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss :
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .boss))"
shows "(is_represented_in_state (in_post_state) (X .boss) (Person) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis" when "(X (\<tau>)) \<noteq> null"
  apply(insert that, case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss is_represented_in_state_def select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: if_split_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss is_represented_in_state_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) (reconst_basetype))))" show "(select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss (?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "typeoid", simp add: select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss_def)
  proof - fix opt show "(((case opt of None \<Rightarrow> null
    | (Some (x)) \<Rightarrow> ((?sel_any) (x)))) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "opt", auto simp: null_fun_def null_option_def bot_option_def)
  proof - fix aa show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t" when "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa))))"
  apply(insert that, drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "?t" when "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r))))" "((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) (reconst_basetype) (e) (\<tau>))"
  apply(insert that, simp add: deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (r))"], simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def Let_def reconst_basetype_def split: if_split_asm)
by(rule) qed
  apply_end((blast)+)
 qed
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed qed
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre :
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Person) .boss@pre))"
shows "(is_represented_in_state (in_pre_state) (X .boss@pre) (Person) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis" when "(X (\<tau>)) \<noteq> null"
  apply(insert that, case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre is_represented_in_state_def select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: if_split_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___bossat_pre is_represented_in_state_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) (reconst_basetype))))" show "(select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss (?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "typeoid", simp add: select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n__boss_def)
  proof - fix opt show "(((case opt of None \<Rightarrow> null
    | (Some (x)) \<Rightarrow> ((?sel_any) (x)))) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "opt", auto simp: null_fun_def null_option_def bot_option_def)
  proof - fix aa show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t" when "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa))))"
  apply(insert that, drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "?t" when "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r))))" "((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) (reconst_basetype) (e) (\<tau>))"
  apply(insert that, simp add: deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (r))"], simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def Let_def reconst_basetype_def split: if_split_asm)
by(rule) qed
  apply_end((blast)+)
 qed
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed qed
  apply_end(simp_all)
 qed

(* 138 ************************************ 904 + 0 *)  (* term Floor1_access.print_access_repr_allinst *)

(* 139 ************************************ 904 + 1 *)
section \<open>Class Model: Towards the Object Instances\<close>

(* 140 ************************************ 905 + 1 *)
text \<open>

The example we are defining in this section comes from the \autoref{fig:Employee-DesignModel-UMLPart-generatededm1_system-states}.
\<close>

(* 141 ************************************ 906 + 1 *)
text_raw \<open>
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:Employee-DesignModel-UMLPart-generatededm1_system-states}
\end{figure}
\<close>

(* 142 ************************************ 907 + 1 *)
text \<open>\<close>

(* 143 ************************************ 908 + 1 *)
text_raw \<open>\<close>

(* 144 ************************************ 909 + 1 *)  (* term Floor1_examp.print_examp_def_st_defs *)
lemmas [simp,code_unfold] = state.defs
                            const_ss

(* 145 ************************************ 910 + 1 *)  (* term Floor1_astype.print_astype_lemmas_id2 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy

(* 146 ************************************ 911 + 1 *)
section \<open>Instance\<close>

(* 147 ************************************ 912 + 2 *)  (* term Floor1_examp.print_examp_instance_defassoc_typecheck_var *)
definition "(typecheck_instance_bad_head_on_lhs_P1_X0_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 (P1) (X0) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)) = ()"
definition "typecheck_instance_extra_variables_on_rhs_P1_X0_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 = (\<lambda>P1 X0 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1. (P1 , P1 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2))"

(* 148 ************************************ 914 + 12 *)  (* term Floor1_examp.print_examp_instance_defassoc *)
definition "oid1 = 1"
definition "oid2 = 2"
definition "oid3 = 3"
definition "oid4 = 4"
definition "oid5 = 5"
definition "oid6 = 6"
definition "oid7 = 7"
definition "oid8 = 8"
definition "oid9 = 9"
definition "oid10 = 10"
definition "oid11 = 11"
definition "inst_assoc1 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((the ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid7] , [oid7]] , [[oid6] , [oid7]] , [[oid2] , [oid2]] , [[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 149 ************************************ 926 + 22 *)  (* term Floor1_examp.print_examp_instance *)
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid1))) (\<lfloor>1300\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid2))) (\<lfloor>1800\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid3) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid3))) (None))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid4))) (\<lfloor>2900\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid5) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid5))) (\<lfloor>3500\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid6))) (\<lfloor>2500\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid7) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid7))) (\<lfloor>3200\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 = ((((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc1))\<rfloor>\<rfloor>)::\<cdot>Person)) .oclAsType(OclAny))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y inst_assoc = (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid8))))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8::\<cdot>OclAny) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid9) (None) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid9))) (\<lfloor>0\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "X0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid10) (None) (None) (None) (None) (\<lfloor>[[oid11]]\<rfloor>))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss) (switch\<^sub>2_01) (oid10))) (None))"
definition "(X0::\<cdot>Person) = ((\<lambda>_. \<lfloor>\<lfloor>(X0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>))"
definition "P1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t inst_assoc = (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<E>\<X>\<T>\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (oid11) (None) (None) (\<lfloor>[[oid11] , [oid11]]\<rfloor>))) (None) (None))"
definition "(P1::\<cdot>Planet) = ((\<lambda>_. \<lfloor>\<lfloor>(P1\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (inst_assoc1))\<rfloor>\<rfloor>))"

(* 150 ************************************ 948 + 1 *)  (* term Floor1_examp.print_examp_instance_defassoc_typecheck *)
ML \<open>(Ty'.check ([(META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 /* unnamed attribute */ \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .boss \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .boss \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .boss \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .boss \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 /* unnamed attribute */ \<cong> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .boss \<cong> Set{}") , (META.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 /* unnamed attribute */ \<cong> Set{}") , (META.Writeln , "X0 .boss \<cong> Set{}") , (META.Writeln , "X0 /* unnamed attribute */ \<cong> Set{}")]) (" error(s)"))\<close>

(* 151 ************************************ 949 + 1 *)
section \<open>State (Floor 1)\<close>

(* 152 ************************************ 950 + 2 *)  (* term Floor1_examp.print_examp_def_st_typecheck_var *)
definition "(typecheck_state_bad_head_on_lhs_\<sigma>\<^sub>1 (\<sigma>\<^sub>1)) = ()"
definition "typecheck_state_extra_variables_on_rhs_\<sigma>\<^sub>1 = (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)"

(* 153 ************************************ 952 + 4 *)  (* term Floor1_examp.print_examp_def_st1 *)
generation_syntax [ shallow (generation_semantics [ design ]) ]
setup \<open>(Generation_mode.update_compiler_config ((K (let open META in Compiler_env_config_ext (true, NONE, Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 12)), I ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 0)), Gen_only_design, SOME (OclClass ((META.SS_base (META.ST "OclAny")), nil, uncurry cons (OclClass ((META.SS_base (META.ST "Galaxy")), uncurry cons (I ((META.SS_base (META.ST "sound")), OclTy_base_void), uncurry cons (I ((META.SS_base (META.ST "moving")), OclTy_base_boolean), uncurry cons (I ((META.SS_base (META.ST "outer_world")), OclTy_collection (Ocl_multiplicity_ext (nil, NONE, uncurry cons (Set, nil), ()), OclTy_collection (Ocl_multiplicity_ext (nil, NONE, uncurry cons (Sequence, nil), ()), OclTy_object (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Planet"))), nil))))), nil))), uncurry cons (OclClass ((META.SS_base (META.ST "Planet")), uncurry cons (I ((META.SS_base (META.ST "wormhole")), OclTy_base_unlimitednatural), uncurry cons (I ((META.SS_base (META.ST "weight")), OclTy_base_integer), nil)), uncurry cons (OclClass ((META.SS_base (META.ST "Person")), uncurry cons (I ((META.SS_base (META.ST "boss")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((META.SS_base (META.ST "oid")), (Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 2), Ocl_ty_class_node_ext ((Code_Numeral.natural_of_integer 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_star, NONE), nil), NONE, nil, ()), (META.SS_base (META.ST "Person")), ()), Ocl_ty_class_node_ext ((Code_Numeral.natural_of_integer 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.natural_of_integer 0)), SOME (Mult_nat ((Code_Numeral.natural_of_integer 1)))), nil), SOME ((META.SS_base (META.ST "boss"))), nil, ()), (META.SS_base (META.ST "Person")), ()), ())), nil))), uncurry cons (I ((META.SS_base (META.ST "salary")), OclTy_base_integer), nil)), nil), nil)), nil)), nil))), uncurry cons (META_instance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1300")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1800")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "2900")))))), nil)), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "3500")))))), nil)), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "2500")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))), NONE, NONE, OclAttrCast ((META.SS_base (META.ST "OclAny")), OclAttrCast ((META.SS_base (META.ST "Person")), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "3200")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))))), nil))), nil), nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"))), SOME ((META.SS_base (META.ST "OclAny"))), NONE, OclAttrNoCast (nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "0")))))), nil)), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X0"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "outer_world")), ShallB_list (uncurry cons (ShallB_list (uncurry cons (ShallB_str ((META.SS_base (META.ST "P1"))), nil)), nil)))), nil)), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "P1"))), SOME ((META.SS_base (META.ST "Planet"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "outer_world")), ShallB_list (uncurry cons (ShallB_list (uncurry cons (ShallB_str ((META.SS_base (META.ST "P1"))), nil)), uncurry cons (ShallB_list (uncurry cons (ShallB_self (Oid ((Code_Numeral.natural_of_integer 10))), nil)), nil))))), nil)), ()), nil))))))))))))), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Galaxy"))), nil), uncurry cons (I ((META.SS_base (META.ST "sound")), OclTy_base_void), uncurry cons (I ((META.SS_base (META.ST "moving")), OclTy_base_boolean), uncurry cons (I ((META.SS_base (META.ST "outer_world")), OclTy_collection (Ocl_multiplicity_ext (nil, NONE, uncurry cons (Set, nil), ()), OclTy_binding (I (NONE, OclTy_collection (Ocl_multiplicity_ext (nil, NONE, uncurry cons (Sequence, nil), ()), OclTy_binding (I (NONE, OclTy_object (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Planet"))), nil))))))))), nil))), nil, false, ())), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Planet"))), uncurry cons (uncurry cons (OclTyCore_pre ((META.SS_base (META.ST "Galaxy"))), nil), nil)), uncurry cons (I ((META.SS_base (META.ST "wormhole")), OclTy_base_unlimitednatural), uncurry cons (I ((META.SS_base (META.ST "weight")), OclTy_base_integer), nil)), nil, false, ())), uncurry cons (META_association (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Person"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_star, NONE), nil), NONE, nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Person"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.natural_of_integer 0)), SOME (Mult_nat ((Code_Numeral.natural_of_integer 1)))), nil), SOME ((META.SS_base (META.ST "boss"))), nil, ())), nil))), ())), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Person"))), uncurry cons (uncurry cons (OclTyCore_pre ((META.SS_base (META.ST "Planet"))), nil), nil)), uncurry cons (I ((META.SS_base (META.ST "salary")), OclTy_base_integer), nil), nil, false, ())), nil))))), uncurry cons (I ((META.ST "P1"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "P1"))), SOME ((META.SS_base (META.ST "Planet"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "outer_world")), ShallB_list (uncurry cons (ShallB_list (uncurry cons (ShallB_str ((META.SS_base (META.ST "P1"))), nil)), uncurry cons (ShallB_list (uncurry cons (ShallB_str ((META.SS_base (META.ST "P1"))), nil)), nil))))), nil)), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 11)))), uncurry cons (I ((META.ST "X0"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X0"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "outer_world")), ShallB_list (uncurry cons (ShallB_list (uncurry cons (ShallB_str ((META.SS_base (META.ST "P1"))), nil)), nil)))), nil)), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 10)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "0")))))), nil)), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 9)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"))), SOME ((META.SS_base (META.ST "OclAny"))), NONE, OclAttrNoCast (nil), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 8)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))), NONE, NONE, OclAttrCast ((META.SS_base (META.ST "OclAny")), OclAttrCast ((META.SS_base (META.ST "Person")), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "3200")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))))), nil))), nil), nil), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 7)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "2500")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"))))), nil))), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 6)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "3500")))))), nil)), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 5)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "2900")))))), nil)), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 4)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (nil), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 3)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1800")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 2)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"))), SOME ((META.SS_base (META.ST "Person"))), NONE, OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1300")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), Oids ((Code_Numeral.natural_of_integer 0), (Code_Numeral.natural_of_integer 1), (Code_Numeral.natural_of_integer 1)))), nil))))))))))), nil, true, false, I (uncurry cons ((META.ST "dot__outer_worldat_pre"), uncurry cons ((META.ST "dot__movingat_pre"), uncurry cons ((META.ST "dot__soundat_pre"), uncurry cons ((META.ST "dot__weightat_pre"), uncurry cons ((META.ST "dot__wormholeat_pre"), uncurry cons ((META.ST "dot__salaryat_pre"), uncurry cons ((META.ST "dot_0___bossat_pre"), nil))))))), uncurry cons ((META.ST "dot__outer_world"), uncurry cons ((META.ST "dot__moving"), uncurry cons ((META.ST "dot__sound"), uncurry cons ((META.ST "dot__weight"), uncurry cons ((META.ST "dot__wormhole"), uncurry cons ((META.ST "dot__salary"), uncurry cons ((META.ST "dot_0___boss"), nil)))))))), uncurry cons ((META.ST "Sequence_Person"), uncurry cons ((META.ST "Set_Person"), uncurry cons ((META.ST "Set_Sequence_Planet"), nil))), I (NONE, false), ()) end))))\<close>
Instance \<sigma>\<^sub>1_object0 :: Person = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 with_only "salary" = 1000, "boss" = self 1 ]
     and \<sigma>\<^sub>1_object1 :: Person = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 with_only "salary" = 1200 ]
     and \<sigma>\<^sub>1_object2 :: Person = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 with_only "salary" = 2600, "boss" = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 ]
     and \<sigma>\<^sub>1_object4 :: Person = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 with_only "salary" = 2300, "boss" = self 2 ]
State[shallow] \<sigma>\<^sub>1 = [ \<sigma>\<^sub>1_object0, \<sigma>\<^sub>1_object1, \<sigma>\<^sub>1_object2, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5, \<sigma>\<^sub>1_object4, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ]

(* 154 ************************************ 956 + 1 *)
section \<open>State (Floor 1)\<close>

(* 155 ************************************ 957 + 2 *)  (* term Floor1_examp.print_examp_def_st_typecheck_var *)
definition "(typecheck_state_bad_head_on_lhs_\<sigma>\<^sub>1' (\<sigma>\<^sub>1')) = ()"
definition "typecheck_state_extra_variables_on_rhs_\<sigma>\<^sub>1' = (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)"

(* 156 ************************************ 959 + 1 *)  (* term Floor1_examp.print_examp_def_st1 *)
State[shallow] \<sigma>\<^sub>1' = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ]

(* 157 ************************************ 960 + 1 *)
section \<open>Transition (Floor 1)\<close>

(* 158 ************************************ 961 + 1 *)  (* term Floor1_examp.print_transition *)
Transition[shallow] \<sigma>\<^sub>1 \<sigma>\<^sub>1'

(* 159 ************************************ 962 + 1 *)
section \<open>Context (Floor 1)\<close>

(* 160 ************************************ 963 + 4 *)  (* term Floor1_ctxt.print_ctxt *)
type_synonym Set_Integer = "(\<AA>, Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
consts dot__contents :: "(\<AA>, '\<alpha>) val \<Rightarrow> (Set_Integer)" ("(_) .contents'(')")
consts dot__contentsat_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (Set_Integer)" ("(_) .contents@pre'(')")
Context[shallow] Person :: contents () : Set(Integer)
  Post : "(\<lambda> result self. (result \<triangleq> if (self .boss \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   else (self .boss .contents()->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   endif))"
  Post : "(\<lambda> result self. (true))"
  Pre : "(\<lambda> self. (false))"

(* 161 ************************************ 967 + 1 *)
section \<open>Context (Floor 1)\<close>

(* 162 ************************************ 968 + 1 *)  (* term Floor1_ctxt.print_ctxt *)
Context[shallow] Person   Inv a : "(\<lambda> self. (self .boss <> null implies (self .salary  \<triangleq>  ((self .boss) .salary))))"

(* 163 ************************************ 969 + 1 *)
section \<open>Context (Floor 1)\<close>

(* 164 ************************************ 970 + 1 *)  (* term Floor1_ctxt.print_ctxt *)
Context[shallow] Planet   Inv A : "(\<lambda> self. (true and (self .weight \<le>\<^sub>i\<^sub>n\<^sub>t \<zero>)))"

end
