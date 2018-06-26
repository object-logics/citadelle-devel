(******************************************************************************
 * HOL-TOY
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

section\<open>Main Translation for: Example (Floor 2)\<close>

theory  Floor2_examp
imports Floor1_examp
begin

definition "init_map_class2 env l =
 (let rbt_str = RBT.bulkload (L.map (\<lambda>(k, _, v). (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list k, v)) (D_input_instance env)) in
  ( rbt_of_class env
  , RBT.lookup (fst (List.fold
                      (\<lambda> toyi (rbt_nat, accu).
                        ( case lookup rbt_str (case Inst_attr_with toyi of
                                                 None \<Rightarrow> inst_name toyi
                                               | Some s \<Rightarrow> s) of
                            None \<Rightarrow> rbt_nat
                          | Some oid_start' \<Rightarrow> RBT.insert (Oid accu) oid_start' rbt_nat
                        , Succ accu))
                      l
                      ( RBT.empty
                      , 0)))
  , lookup rbt_str))"

definition "merge_unique_gen f l = List.fold (List.fold (\<lambda>x. case f x of Some (x, v) \<Rightarrow> RBT.insert x v | None \<Rightarrow> id)) l RBT.empty"
definition "merge_unique f l = RBT.entries (merge_unique_gen f l)"
definition "merge_unique' f =
   L.map snd
 o RBT.entries
 o (\<lambda>l.
     List.fold
       (\<lambda>((k, _), e) rbt.
         RBT.insert k
                    (case RBT.lookup rbt k of
                       None \<Rightarrow> [e]
                     | Some l \<Rightarrow> e # l)
                    rbt)
       l
       RBT.empty)
 o merge_unique (\<lambda> ((a, n), b). Some ((oidGetInh a, n), (a, b)))
 o L.map (L.map (\<lambda>(oid, e) \<Rightarrow> ((oid, f e), e)))"
definition "merge_unique'' l =
  L.map (L.map (map_prod id (\<lambda> ToyDefCoreBinding (_, toyi) \<Rightarrow> toyi)))
        (merge_unique' (\<lambda> ToyDefCoreBinding (s, _) \<Rightarrow> String.to_list s) l)"

definition "map_tail f =
 (let f = map_prod (Term_oid var_oid_uniq o oidGetInh) f in
  L.map (\<lambda> x # xs \<Rightarrow>
          map_prod id
           (\<lambda>x. L.flatten (x # L.map (snd o f) xs))
           (f x)))"

definition "print_examp_def_st_locale_distinct = \<open>distinct_oid\<close>"
definition "print_examp_def_st_locale_metis = M.metis (L.map T.thm [print_examp_def_st_locale_distinct, \<open>distinct_length_2_or_more\<close>])"
definition "print_examp_def_st_locale_aux l =
 (let b = \<lambda>s. Term_basic [s] in
  map_prod
    id
    L.flatten
    (L.split
      (map_tail
        (\<lambda> toyi.
           let n = inst_name toyi
           ; ty = inst_ty toyi
           ; f = \<lambda>s. s @@ String.isub ty
           ; name_pers = print_examp_instance_name f n in
           [ ( [(b name_pers, Typ_base (f datatype_name))], None)
           , ( [(b n, Typ_base (wrap_toyty ty))]
             , Some (hol_definition n, Term_rewrite (b n) \<open>=\<close> (Term_lambda wildcard (Term_some (Term_some (b name_pers)))))) ])
        l)))"

definition "print_examp_def_st_locale_make f_name f_spec l =
 (let (oid, l_fix_assum) = print_examp_def_st_locale_aux l
    ; ty_n = \<open>nat\<close> in
  \<lparr> HolThyLocale_name = f_name
  , HolThyLocale_header = L.flatten
                            [ [ ( L.map (\<lambda>x. (x, Typ_base ty_n)) oid
                                , Some ( print_examp_def_st_locale_distinct
                                       , Term_app \<open>distinct\<close> [let e = Term_list oid in
                                                                if oid = [] then Term_annot' e (ty_n @@ \<open> list\<close>) else e])) ]
                            , l_fix_assum
                            , f_spec ] \<rparr>)"

definition "print_examp_def_st_locale_sort env l =
  merge_unique' (String.to_list o inst_name)
                (L.map (\<lambda> ToyDefCoreBinding name \<Rightarrow> case String.assoc name (D_input_instance env) of
                                                      Some n \<Rightarrow> [flip n]) l)"

definition "filter_locale_interp =
    L.split
  o map_tail
      (let a = \<lambda>f x. Term_app f [x]
       ; b = \<lambda>s. Term_basic [s]
       ; c = Term_paren \<open>\<lceil>\<close> \<open>\<rceil>\<close>
       ; var_tau = \<open>\<tau>\<close> in
       \<lambda> toyi \<Rightarrow>
        let n = inst_name toyi in
        [ c (c (a n (b var_tau)))
        , b n])"

definition "print_examp_def_st_locale_name n = \<open>state_\<close> @@ n"
definition "print_examp_def_st_locale = (\<lambda> ToyDefSt n l \<Rightarrow> \<lambda>env.
 (\<lambda>d. (d, env))
  (print_examp_def_st_locale_make
    (print_examp_def_st_locale_name n)
    []
    (print_examp_def_st_locale_sort env l)))"

definition "print_examp_def_st_mapsto_gen f =
  L.map
    (\<lambda>(cpt, ocore).
        let b = \<lambda>s. Term_basic [s]
          ; (toyi, exp) = case ocore of
               ToyDefCoreBinding (name, toyi) \<Rightarrow>
                 (toyi, Some (b (print_examp_instance_name (\<lambda>s. s @@ String.isub (inst_ty toyi)) name))) in
        f (cpt, ocore) toyi exp)"

definition "print_examp_def_st_mapsto l = L.bind id id
 (print_examp_def_st_mapsto_gen
    (\<lambda>(cpt, _) toyi. map_option (\<lambda>exp.
      Term_binop (Term_oid var_oid_uniq (oidGetInh cpt)) \<open>\<mapsto>\<close> (Term_app (datatype_in @@ String.isub (inst_ty toyi)) [exp])))
    l)"

definition "print_examp_def_st2 = (\<lambda> ToyDefSt name l \<Rightarrow> \<lambda>env.
 (\<lambda>(l, l_st). (L.map O'.definition l, env \<lparr> D_input_state := (String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name, l_st) # D_input_state env \<rparr>))
  (let b = \<lambda>s. Term_basic [s]
     ; l = L.map (\<lambda> ToyDefCoreBinding name \<Rightarrow> map_option (Pair name) (String.assoc name (D_input_instance env))) l
     ; (rbt, (map_self, map_username)) =
         (init_map_class2
           env
           (L.map (\<lambda> Some (_, toyi, _) \<Rightarrow> toyi | None \<Rightarrow> toy_instance_single_empty) l)
          :: (_ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _) \<Rightarrow> _
                        \<Rightarrow> (toy_ty_class option \<times> (toy_ty \<times> toy_data_shallow) option) list) option)) \<times> _ \<times> _)
     ; (l_st, l_assoc) = L.mapM (\<lambda> o_n l_assoc.
           case o_n of
              Some (name, toyi, cpt) \<Rightarrow> ([(cpt, ToyDefCoreBinding (name, toyi))], (toyi, cpt) # l_assoc)
            | None \<Rightarrow> ([], l_assoc)) l []
     ; l_st = L.unique oidGetInh (L.flatten l_st) in

   ( [ Definition (Term_rewrite (b name) \<open>=\<close> (Term_app \<open>state.make\<close>
        ( Term_app \<open>Map.empty\<close> (case print_examp_def_st_mapsto l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
        # [ print_examp_def_st_assoc (snd o rbt) map_self map_username l_assoc ]))) ]
   , l_st)))"

definition "print_examp_def_st_perm_name name = S.flatten [\<open>perm_\<close>, name]"
definition "print_examp_def_st_perm = (\<lambda> _ env.
 (\<lambda> l. (L.map O'.lemma l, env))
  (let (name, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String id (hd (D_input_state env))
     ; expr_app = print_examp_def_st_mapsto (rev l_st)
     ; b = \<lambda>s. Term_basic [s]
     ; d = hol_definition
     ; (l_app, l_last) =
         case l_st of [] \<Rightarrow> ([], C.by [M.simp_add [d name]])
         | [_] \<Rightarrow> ([], C.by [M.simp_add [d name]])
         | _ \<Rightarrow>
           ( [ M.simp_add [d name]]
             # L.flatten (L.map (\<lambda>i_max. L.map (\<lambda>i. [M.subst_l (L.map String.nat_to_digit10 [i_max - i]) (T.thm \<open>fun_upd_twist\<close>), print_examp_def_st_locale_metis]) (List.upt 0 i_max)) (List.upt 1 (List.length l_st)))
           , C.by [M.simp]) in
   case expr_app of None \<Rightarrow> [] | Some expr_app \<Rightarrow>
   [ Lemma
       (print_examp_def_st_perm_name name)
       [Term_rewrite (b name) \<open>=\<close> (Term_app \<open>state.make\<close>
          (Term_app \<open>Map.empty\<close> expr_app # [Term_app var_assocs [b name]]))]
       l_app
       l_last ]))"

definition "get_state f = (\<lambda> ToyDefPP _ s_pre s_post \<Rightarrow> \<lambda> env.
  let get_state = let l_st = D_input_state env in \<lambda>ToyDefPPCoreBinding s \<Rightarrow> (s, case String.assoc s l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
    ; (s_pre, l_pre) = get_state s_pre
    ; (s_post, l_post) = case s_post of None \<Rightarrow> (s_pre, l_pre) | Some s_post \<Rightarrow> get_state s_post in
  f (s_pre, l_pre)
    (s_post, l_post)
    ((s_pre, l_pre) # (if s_pre \<triangleq> s_post then
                         []
                       else
                         [ (s_post, l_post) ]))
    env)"

definition "print_transition_locale_aux l =
 (let (oid, l_fix_assum) = print_examp_def_st_locale_aux (merge_unique'' [l]) in
  L.flatten [oid, L.flatten (L.map (L.map fst o fst) l_fix_assum) ])"

definition "print_transition_locale_name s_pre s_post = \<open>transition_\<close> @@ s_pre @@ \<open>_\<close> @@ s_post"
definition "print_transition_locale = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) l_pre_post. Pair
 (print_examp_def_st_locale_make
    (print_transition_locale_name s_pre s_post)
    (L.map (\<lambda>(s, l). ([], Some (s, Term_app
                                        (print_examp_def_st_locale_name s)
                                        (print_transition_locale_aux l))))
              l_pre_post)
    (merge_unique'' [l_pre, l_post])))"

definition "print_transition_interp = get_state (\<lambda> _ _.
 Pair o L.map O'.interpretation o L.map
  (\<lambda>(s, l).
    let n = print_examp_def_st_locale_name s in
    Interpretation n n (print_transition_locale_aux l)
                       (C.by [M.rule (T.thm s)])))"

end
