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

chapter{* Part ... *}

theory  Class_model
imports "../../src/compiler/core/Core_init"
begin

definition "print_class =
 (\<lambda> (C_out_OclAny, s) \<Rightarrow> S.flatten [\<open>Class \<close>, s, \<open> End\<close>]
  | (C_out_simple s1, s2) \<Rightarrow> S.flatten [\<open>Class \<close>, s2, \<open> < \<close>, s1, \<open> End\<close>])"

definition \<open>print_abr sprintf_int write_file =
  (let sprintf_int = sprintf_int o natural_of_nat
     ; S_flatten_n = S.flatten o L.map (\<lambda>s. S.flatten [s, \<lless>[CHR 0x0A]\<ggreater>]) in
  L.flatten o L.flatten o L.map (\<lambda> (nb_child, deep).
    let body = L.map print_class (fst (mk_tree nb_child deep 0))
      ; tree_name = S.flatten [\<open>Tree_\<close>, sprintf_int nb_child, \<open>_\<close>, sprintf_int deep] in

    L.map
      (\<lambda> ((gen_mode, gen_comp), gen_import, gen_init, gen_flush).
        L.map
          (\<lambda>(comp, comp2).
            let filename = S.flatten [tree_name, \<open>_\<close>, gen_mode, if String.to_list comp = [] then \<open>\<close> else S.flatten [\<open>_\<close>, comp]] in
            write_file
              (S.flatten [filename, \<open>.thy\<close>])
              (L.flatten
                [ [ S.flatten [\<open>theory \<close>, filename, \<open> imports \<close>, gen_import, \<open> \<close>,
                               \<open>"../../src/compiler/Generator_dynamic_sequential"\<close>,
                               \<open> begin\<close>]
                  , gen_init comp comp2]
                , body
                , [ \<open>\<close>
                  , S.flatten [\<open>(* \<close>, String.nat_to_digit10 (length body), \<open> *)\<close> ]
                  , \<open>\<close>
                  , gen_flush
                  , \<open>\<close>
                  , \<open>end\<close> ] ])) gen_comp)
      [ ( (\<open>deep\<close>, [ (\<open>Haskell\<close>, \<open>\<close>)
                   , (\<open>OCaml\<close>, \<open>module_name M\<close>)
                   , (\<open>Scala\<close>, \<open>module_name M\<close>)
                   , (\<open>SML\<close>, \<open>module_name M\<close>)
                   , (\<open>self\<close>, \<open>\<close>) ])
        , \<open>\<close>
        , \<lambda> comp comp2.
            S_flatten_n [            \<open>generation_syntax [ deep\<close>
                        ,            \<open>                      (generation_semantics [ analysis (*, oid_start 10*) ])\<close>
                        ,            \<open>                      skip_export\<close>
                        , S.flatten [\<open>                      (THEORY \<close>, tree_name, \<open>_generated\<close>, \<open>_\<close>, comp, \<open>)\<close>]
                        , S.flatten [\<open>                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]\<close>]
                        , S.flatten [\<open>                               "../../../src/compiler/Generator_dynamic_sequential")\<close>]
                        ,            \<open>                      SECTION\<close>
                        , S.flatten [\<open>                      [ in \<close>, comp, \<open> \<close>, comp2, \<open> ]\<close>]
                        , S.flatten [\<open>                      (output_directory "./doc") ]\<close>] ]
        , S_flatten_n [ \<open>generation_syntax deep flush_all\<close> ])
      , ( (\<open>shallow\<close>, [(\<open>\<close>, \<open>\<close>)])
        , S.flatten [ \<open>"../../src/UML_Main"\<close>, \<open> \<close>
                    , \<open>"../../src/compiler/Static"\<close>  ]
        , \<lambda>_ _. S_flatten_n [ \<open>generation_syntax [ shallow (generation_semantics [ analysis ]) ]\<close> ]
        , \<open>End!\<close>) ]))\<close>

definition "main sprintf_int write_file = print_abr (\<lambda>n. \<lless>sprintf_int n\<ggreater>) (\<lambda>f l. write_file (String.to_list f) (L.map String.to_list l))
 (let f = List.fold (\<lambda> n l. (1, n) # (n, 1) # l) in
  [ (* 0 *) (1, 0)
  , (* 1 *) (1, 1) ]
 @@@@
  f [ 2, 3, 4, 5, 6, 7(*, 8, 9*) ]
    [ (* 6 *) (2, 2) ]

 @@@@
  f [ 12, 14, 20, 30, 39, 42, 56 ]
    [ (* 14 *) (2, 3)
    , (* 30 *) (2, 4)
    , (* 12 *) (3, 2)
    , (* 39 *) (3, 3)
    , (* 20 *) (4, 2)
    , (* 30 *) (5, 2)
    , (* 42 *) (6, 2)
    , (* 56 *) (7, 2) ]
(*
 @@@@
  f [ 62, 72, 84, 90 ]
    [ (* 62 *) (2, 5)
    , (* 84 *) (4, 3)
    , (* 72 *) (8, 2)
    , (* 90 *) (9, 2) ]*))"
(*
export_code open main
  in OCaml module_name M file "class_model_isabelle.ml"
*)
end
