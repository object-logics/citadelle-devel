(******************************************************************************
 * A Meta-Model for the Isabelle API
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

section\<open>Instantiating the Printer for (Pure) Term\<close>

theory  Printer_Pure
imports Meta_Pure
        Printer_init
begin

context Print
begin

fun of_pure_typ where "of_pure_typ e = (\<lambda>
    Type s l \<Rightarrow> if s \<triangleq> \<langle>STR ''fun''\<rangle> then
                  \<open>(%s)\<close> (String_concat \<open> \<Rightarrow> \<close> (List.map of_pure_typ l))
                else if s \<triangleq> \<langle>STR ''Product_Type.prod''\<rangle> then
                  \<open>(%s)\<close> (String_concat \<open> \<times> \<close> (List.map of_pure_typ l))
                else
                  \<open>%s%s\<close> (case l of [] \<Rightarrow> \<open>\<close>
                                  | _ \<Rightarrow> \<open>(%s) \<close> (String_concat \<open>, \<close> (List.map of_pure_typ l)))
                         (To_string s)
  | TFree _ _ \<Rightarrow> \<open>_\<close>) e"

definition "pure_typ0 show_t s t =
 (let s = To_string s in
  if show_t then
    \<open>(%s :: %s)\<close> s (of_pure_typ t)
  else
    s)"

fun of_pure_term where "of_pure_term show_t l e = (\<lambda>
    Const s t \<Rightarrow> pure_typ0 show_t s t
  | Free s t \<Rightarrow> pure_typ0 show_t s t
  | App t1 t2 \<Rightarrow> \<open>(%s) (%s)\<close> (of_pure_term show_t l t1) (of_pure_term show_t l t2)
  | Abs s st t \<Rightarrow>
      \<open>(\<lambda> %s. %s)\<close> (pure_typ0 show_t s st) (of_pure_term show_t (To_string s # l) t)
  | Bound n \<Rightarrow> \<open>%s\<close> (l ! nat_of_natural n)) e"

end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.pure_typ0_def

  \<comment> \<open>fun\<close>
  Print.of_pure_typ.simps
  Print.of_pure_term.simps

end
