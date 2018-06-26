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

chapter{* Part ... *}

theory Gram
imports Main
  keywords "tex" "no_tex" "tex_raw" "init" "remove" "add" "drop" "keep" "<<<" ">>>"
       and "print_syntax'" :: thy_decl
begin

ML{*

datatype name = B of binding | S of string
datatype ('a, 'b, 'c) parse_term = Grammar of 'a * 'b
                                 | Grammar_noprio of 'a
                                 | HOL of 'c

datatype 'a rewrite = NoRewrite | R_underscore of 'a | RConst of 'a | RType of 'a

datatype 'a gen_mode = Gen_add of 'a | Gen_add_raw | Gen_remove

datatype 'a filter = Filter_on of int option | Filter_off of int option | Filter_data of 'a

structure Data_rule = Theory_Data
  (type T = Symtab.set Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val parse_name = Parse.long_ident >> S || Parse.binding >> B
val parse_int = Scan.optional (Parse.sym_ident >> (fn "-" => false | _ => Scan.fail "syntax error")) true -- Parse.number >> (fn (b, n) => case Int.fromString n of SOME s => if b then s else 0 - s | _ => Scan.fail "syntax error")

val parse_grammar =
        (   parse_name --| Parse.$$$ "="
         -- Scan.repeat ((parse_name -- Scan.option (Parse.$$$ "[" |-- parse_int --| Parse.$$$ "]") >>
                                (fn (t, prio) => case prio of NONE => HOL t | SOME prio => Grammar (t, prio))))
         -- (Scan.option (Parse.$$$ "=>" |-- Parse.string) >>
              (fn NONE => NoRewrite
                | SOME s => case Symbol.explode s of "\<^type>" :: s => RType (implode s)
                | "\<^const>" :: s => RConst (implode s)
                | "_" :: s => R_underscore (implode s)
                | _ => Scan.fail "error syntax"))
         --| Parse.$$$ "(" -- parse_int --| Parse.$$$ ")"
         -- (Scan.option (   @{keyword "no_tex"} >> K Gen_remove
                          || @{keyword "tex_raw"} >> K Gen_add_raw
                          || @{keyword "tex"} |-- Parse.document_source >> Gen_add)
             ))

val s_of_name = fn B b => Binding.name_of b | S s => s
fun string_of_rule ((((gram_name, l), rew), prio), doc) =
  s_of_name gram_name ^ String.concat (map (fn Grammar (n,_) => s_of_name n | Grammar_noprio n => s_of_name n | HOL n => s_of_name n) l)

fun show_text l =
  let val terminals = Symtab.make_set Lexicon.terminals
      val tab = fold (fn ((((gram_name, l), rew), prio), doc) =>
                        Symtab.insert (op =) (s_of_name gram_name, ()))
                     l
                     terminals
      val s = String.concat (List.concat (map (fn ((((gram_name, l), rew), prio), doc) =>
        let val l = map (fn HOL s => if Symtab.lookup tab (s_of_name s) = NONE then
                                       HOL s
                                     else
                                       Grammar_noprio s
                          | x => x) l
            fun gram t prio =
              let val s0 = s_of_name t
                  val s = "$\\text{@{text \"" ^ s0 ^ "\"}}" ^ (case prio of NONE => "" | SOME i => "^{\\text{\\color{GreenYellow}" ^ Int.toString i ^ "}}") ^ "$" in
              (if Symtab.lookup terminals s0 = NONE then s else "\\fbox{" ^ s ^ "}") ^ " "
              end
            fun output_text f =
                              [ "text\<open>{\\color{Gray}($\\text{@{text \""
                              ^ s_of_name gram_name ^ "\"}}^{\\text{\\color{GreenYellow}" ^ Int.toString prio ^ "}}$"
                              ^ ")} "
                              ^ String.concat (map (fn Grammar (t, p) => gram t (SOME p)
                                                     | Grammar_noprio t => gram t NONE
                                                     | HOL t => "\\colorbox{Apricot}{" ^ "" ^ f (s_of_name t) ^ "" ^ "} ") l)
                              ^ (case rew of NoRewrite => "\\hfill{\\small\\color{Gray} (none)}"
                                 | _ =>
                                    let val (s, ty) =
                                          case rew of R_underscore s => (s, NONE)
                                                    | RConst s => (s, SOME "const")
                                                    | RType s => (s, SOME "type") in
                                      "\\hfill{\\color{SkyBlue}"
                                    ^ (case ty of NONE => "\\fbox{\\small\\color{Gray} @{text \"" ^ s ^ "\"}}"
                                                | SOME ty => "\\fbox{\\small @{text \"" ^ s ^ "\"}}\\text{\\space\\color{Black}@{text \"" ^ ty ^ "\"}}")
                                    ^ "}"
                                    end)
                              ^ "\<close>\n" ] in
        case doc of SOME Gen_remove => []
                  | SOME Gen_add_raw => output_text (fn "\<^bsub>" => "\\rotatebox[origin=c]{315}{$\\Rightarrow$}"
                                                      | "\<^esub>" => "\\rotatebox[origin=c]{45}{$\\Leftarrow$}"
                                                      | "op" => "\\isa{op}"
                                                      | "\<longlongrightarrow>" => "$\\xrightarrow{\\hphantom{AAA}}$"
                                                      | "\<longlonglongrightarrow>" => "$\\xrightarrow{\\hphantom{AAAA}}$")
                  | _ => List.concat [ output_text (fn s => "@{text \"" ^ s ^ "\"}")
                                     , case doc of SOME (Gen_add s) => [ "(* *) text\<open>" ^ Input.source_content s ^ "\<close>\n" ]
                                                 | _ => []]
        end) l)) in
  writeln (Active.sendback_markup_command s)
  end

fun msg_err msg = "The previous counter is already " ^ msg ^ " (this particular overlapping is not yet implemented)."

fun check_filter_on b = fn Filter_on (SOME n) => if n >= 1 then error (msg_err "on") else b
                      | _ => b

fun check_filter_on_all b = fn Filter_on _ => error (msg_err "on")
                      | _ => b

fun check_filter_off b = fn Filter_off (SOME n) => if n >= 1 then error (msg_err "off") else b
                      | _ => b

fun check_filter_off_all b = fn Filter_off _ => error (msg_err "off")
                      | _ => b

fun filter_drop l0 =
  fold (fn Filter_on NONE => (fn (f, accu) => (check_filter_off (Filter_on NONE) f, accu))
         | Filter_off NONE => (fn (f, accu) => (check_filter_on (Filter_off NONE) f, accu))
         | Filter_on (SOME n) => (fn (f, accu) => (check_filter_on_all (check_filter_off (Filter_on (SOME (n - 1))) f) f, accu))
         | Filter_off (SOME n) => (fn (f, accu) => (check_filter_off_all (check_filter_on (Filter_off (SOME (n - 1))) f) f, accu))
         | Filter_data x => fn (b, accu) => ( case b of Filter_on (SOME n) => if n <= 0 then Filter_off NONE else Filter_on (SOME (n - 1))
                                                      | Filter_off (SOME n) => if n <= 0 then Filter_on NONE else Filter_off (SOME (n - 1))
                                                      | x => x
                                            , case b of Filter_on _ => x :: accu
                                                      | Filter_off _ => accu))
       l0
       (Filter_on NONE, [])
  |> snd
  |> rev

val _ =
  Outer_Syntax.command @{command_keyword print_syntax'}
    "print inner syntax of context"
    ((@{keyword "init"} >> K true || @{keyword "remove"} >> K false)
     -- Parse.name
     -- Scan.optional (@{keyword "add"} |-- Parse.list1 Parse.name) []
     -- Parse.binding --| Parse.$$$ ":"
     -- Scan.repeat (let val parse_n = Scan.option Parse.number >> (SOME o
                             (fn NONE => 1
                               | SOME n => case Int.fromString n of NONE => error "Int.fromString"
                                                                  | SOME n => if n <= 0 then error "semantics not yet implemented" else n)) in
                        @{keyword "<<<"} >> K (Filter_on NONE)
                     || @{keyword ">>>"} >> K (Filter_off NONE)
                     || (@{keyword "keep"} |-- parse_n) >> Filter_on
                     || (@{keyword "drop"} |-- parse_n) >> Filter_off
                     || parse_grammar >> Filter_data
                     end) >> (fn ((((init, name), l_add), _), l0) =>
    Toplevel.theory (fn thy =>
      if init then
        let val _ = show_text (filter_drop l0) in
        Data_rule.map (Symtab.map_default (name, Symtab.empty)
          (fold (fn Filter_data rule => Symtab.insert (op =) (string_of_rule rule, ()) | _ => I) l0)) thy
        end
      else
        let val _ = show_text (List.filter
                                (let val set =
                                       case Symtab.lookup (Data_rule.get thy) name of SOME s => s | _ => Symtab.empty in
                                 fn e => Symtab.lookup set (string_of_rule e) = NONE
                                         orelse List.exists (case e of ((((gram_name, _), _), _), _) => fn n => s_of_name gram_name = n) l_add
                                 end)
                                (filter_drop l0)) in
        thy
        end)))

*}

end
