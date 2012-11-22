header{* Part II: State Operations and Objects *}

theory OCL_state
imports OCL_lib
begin

subsection{* Recall: The generic structure of States*}

text{* Next we will introduce the foundational concept of an object id (oid), 
which is just some infinite set.  *}

type_synonym oid = ind

text{* States are just a partial map from oid's to elements of an object universe @{text "'\<AA>"},
and state transitions pairs of states...  *}
type_synonym ('\<AA>)state = "oid \<rightharpoonup> '\<AA> "

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

text{* Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have 
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"


subsection{* Referential Object Equality in States*}

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition  gen_ref_eq :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean" 
where      "gen_ref_eq x y
            \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"


lemma gen_ref_eq_object_strict1[simp] : 
"(gen_ref_eq x invalid) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict2[simp] : 
"(gen_ref_eq invalid x) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict3[simp] : 
"(gen_ref_eq x null) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict4[simp] : 
"(gen_ref_eq null x) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma cp_gen_ref_eq_object: 
"(gen_ref_eq x y \<tau>) = (gen_ref_eq (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: gen_ref_eq_def StrongEq_def invalid_def  cp_defined[symmetric])

lemmas cp_intro[simp,intro!] = 
       OCL_core.cp_intro
       cp_gen_ref_eq_object[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "gen_ref_eq"]]

text{* Finally, we derive the usual laws on definedness for (generic) object equality:*}
lemma gen_ref_eq_defargs: 
"\<tau> \<Turnstile> (gen_ref_eq x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: gen_ref_eq_def OclValid_def true_def invalid_def
             defined_def invalid_def bot_fun_def bot_option_def
        split: bool.split_asm HOL.split_if_asm)


subsection{* Further requirements on States*}
text{* A key-concept for linking strict referential equality to
       logical equality: in well-formed states (i.e. those
       states where the self (oid-of) field contains the pointer
       to which the object is associated to in the state), 
       referential equality coincides with logical equality. *}

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> ran(fst \<tau>). \<lceil>fst \<tau> (oid_of x)\<rceil> = x) \<and>
                (\<forall> x \<in> ran(snd \<tau>). \<lceil>snd \<tau> (oid_of x)\<rceil> = x))"

text{* This is a generic definition of referential equality:
Equality on objects in a state is reduced to equality on the
references to these objects. As in HOL-OCL, we will store
the reference of an object inside the object in a (ghost) field.
By establishing certain invariants ("consistent state"), it can
be assured that there is a "one-to-one-correspondance" of objects
to their references --- and therefore the definition below
behaves as we expect. *}
text{* Generic Referential Equality enjoys the usual properties:
(quasi) reflexivity, symmetry, transitivity, substitutivity for
defined values. For type-technical reasons, for each concrete
object type, the equality @{text "\<doteq>"} is defined by generic referential
equality. *}

theorem strictEqGen_vs_strongEq: 
"WFF \<tau> \<Longrightarrow> \<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> 
           (x \<tau> \<in> ran (fst \<tau>) \<and> y \<tau> \<in> ran (fst \<tau>)) \<and>
           (x \<tau> \<in> ran (snd \<tau>) \<and> y \<tau> \<in> ran (snd \<tau>)) \<Longrightarrow> (* x and y must be object representations
                                                          that exist in either the pre or post state *) 
           (\<tau> \<Turnstile> (gen_ref_eq x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(auto simp: gen_ref_eq_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

text{* So, if two object descriptions live in the same state (both pre or post), the referential
equality on objects implies in a WFF state the logical equality. Uffz. *}

section{* Miscillaneous: Initial States (for Testing and Code Generation) *}

definition \<tau>\<^isub>0 :: "('\<AA>)st"
where     "\<tau>\<^isub>0 \<equiv> (Map.empty,Map.empty)"


subsection{* Generic Operations on States *}

text{* In order to denote OCL-types occuring in OCL expressions syntactically --- as, for example, 
as "argument" of allInstances --- we use the inverses of the injection functions into the object
universes; we show that this is sufficient "characterization". *}

definition allinstances :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ .oclAllInstances'(')")
where  "((H).oclAllInstances()) \<tau> = 
                 Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(snd \<tau>) \<inter> {x. \<exists> y. y=H x}) \<rfloor>\<rfloor> "

definition allinstancesATpre :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ .oclAllInstances@pre'(')")
where  "((H).oclAllInstances@pre()) \<tau> = 
                 Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(fst \<tau>) \<inter> {x. \<exists> y. y=H x}) \<rfloor>\<rfloor> "

lemma "\<tau>\<^isub>0 \<Turnstile> H .oclAllInstances() \<triangleq> Set{}"
sorry


lemma "\<tau>\<^isub>0 \<Turnstile> H .oclAllInstances@pre() \<triangleq> Set{}"
sorry

theorem state_update_vs_allInstances: 
assumes "oid\<notin>dom \<sigma>'"
and     "cp P" 
shows   "((\<sigma>, \<sigma>'(oid\<mapsto>Object)) \<Turnstile> (P(Type .oclAllInstances()))) =  
          ((\<sigma>, \<sigma>') \<Turnstile> (P((Type .oclAllInstances())->including(\<lambda> _. Some(Some((the_inv Type) Object)))))) "
sorry

theorem state_update_vs_allInstancesATpre: 
assumes "oid\<notin>dom \<sigma>"
and     "cp P" 
shows   "((\<sigma>(oid\<mapsto>Object), \<sigma>') \<Turnstile> (P(Type .oclAllInstances@pre()))) =  
          ((\<sigma>, \<sigma>') \<Turnstile> (P((Type .oclAllInstances@pre())->including(\<lambda> _. Some(Some((the_inv Type) Object)))))) "
sorry


definition oclisnew:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsNew'(')")
where "X .oclIsNew() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau> 
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(fst \<tau>) \<and> oid_of (X \<tau>) \<in> dom(snd \<tau>)\<rfloor>\<rfloor>
                              else invalid \<tau>)" 

text{* The following predicate --- which is not part of the OCL standard descriptions ---
provides a simple, but powerful means to describe framing conditions. For any formal
approach, be it animation of OCL contracts, test-case generation or die-hard theorem
proving, the specification of the part of a system transistion that DOES NOT CHANGE
is of premordial importance. The following operator establishes the equality between
old and new objects in the state (provided that they exist in both states), with the 
exception of those objects 
*}

definition oclismodified ::"('\<AA>::object,'\<alpha>::{null,object})Set \<Rightarrow> '\<AA> Boolean" 
                        ("_->oclIsModifiedOnly'(')")
where "X->oclIsModifiedOnly() \<equiv> (\<lambda>(\<sigma>,\<sigma>').  let  X' = (oid_of ` \<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>);
                                                 S = ((dom \<sigma> \<inter> dom \<sigma>') - X')
                                            in if (\<delta> X) (\<sigma>,\<sigma>') = true (\<sigma>,\<sigma>') 
                                               then \<lfloor>\<lfloor>\<forall> x \<in> S. \<sigma> x = \<sigma>' x\<rfloor>\<rfloor>
                                               else invalid (\<sigma>,\<sigma>'))"


definition atSelf :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@pre(_)")
where "x @pre H = (\<lambda>\<tau> . if (\<delta> x) \<tau> = true \<tau> 
                        then if oid_of (x \<tau>) \<in> dom(fst \<tau>) \<and> oid_of (x \<tau>) \<in> dom(snd \<tau>)
                             then  H \<lceil>(fst \<tau>)(oid_of (x \<tau>))\<rceil>
                             else invalid \<tau>
                        else invalid \<tau>)"


theorem framing:
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding(x))->oclIsModifiedOnly()"
      and    represented_x: "\<tau> \<Turnstile> \<delta>(x @pre H)"
      and    H_is_typerepr: "inj H"
      shows "\<tau> \<Turnstile> (x  \<triangleq>  (x @pre H))"
sorry


end