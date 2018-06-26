(******************************************************************************
 * LICENSE
 *
 * Copyright (c) 2017-2018 Virginia Tech, USA
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

theory LICENSE0
  imports Main
  keywords "portions"
       and "project" "country" "holder" "copyright" "license"
           "check_license" "insert_license" "map_license" :: thy_decl
begin

ML\<open>
structure Resources' = struct
  fun check_path' check_file ctxt dir (name, pos) =
    let
      fun err msg pos = error (msg ^ Position.here pos)
      val _ = Context_Position.report ctxt pos Markup.language_path;
  
      val path = Path.append dir (Path.explode name) handle ERROR msg => err msg pos;
      val path' = Path.expand path handle ERROR msg => err msg pos;
      val _ = Context_Position.report ctxt pos (Markup.path (Path.smart_implode path));
      val _ =
        (case check_file of
          NONE => path
        | SOME check => (check path handle ERROR msg => err msg pos));
    in path' end

  fun check_dir thy = check_path' (SOME File.check_dir)
                                  (Proof_Context.init_global thy)
                                  (Resources.master_directory thy)
end

fun fold_dir f path =
  File.fold_dir
    (fn s =>
      let val path = Path.append path (Path.explode s)
      in if File.is_dir path then fold_dir f path else f path end)
    path
\<close>

ML\<open>
datatype ('a, 'b) either = Left of 'a | Right of 'b

fun the_left (Left a) = a

signature OBJECT = sig
  type T
  val key : string
  val pretty : T -> string
end

functor Theory_Data' (Obj : OBJECT) : THEORY_DATA = Theory_Data
  (type T = Obj.T Name_Space.table
   val empty = Name_Space.empty_table Obj.key
   val extend = I
   val merge = Name_Space.merge_tables)

val pretty_input = Input.source_content #> split_lines #> trim (fn s => s = "") #> cat_lines

structure Country0 : OBJECT = struct
  type T = Input.source
  val key = "country"
  val pretty = pretty_input
end

structure Country = Theory_Data' (Country0)

structure Holder0 : OBJECT = struct
  type T = Input.source list * Country0.T option
  val key = "holder"
  fun pretty (l, country) = 
    let val sep = ", " in
      String.concatWith sep (map (fn s => s |> Input.source_explode |> Symbol_Pos.trim_blanks |> Symbol_Pos.content) l)
      ^ (case country of NONE => "" | SOME country => sep ^ Country0.pretty country)
    end
end

structure Holder = Theory_Data' (Holder0)

datatype date = D_interval of int (*date min*) * int (*date max*)
              | D_discrete of int list

structure Date0 : OBJECT where type T = date = struct
  type T = date
  val key = "date"
  val pretty = fn D_interval (d_min, d_max) => Int.toString d_min ^ "-" ^ Int.toString d_max
                | D_discrete l => String.concatWith "," (map Int.toString l)
end

structure Copyright0 : OBJECT = struct
  type T = (bool (*false: portions copyright*) * Date0.T * Holder0.T list) list
  val key = "copyright"
  fun pretty l =
    let
      val s_copy = "Copyright (c) "
      fun s_portions b = if b then Symbol.spaces (String.size s_copy) else "Portions " ^ s_copy
    in
      case map (fn (b, date, l) => (b, case l of h :: hs => let val s_date = Date0.pretty date ^ " " 
                                                            in s_date ^ Holder0.pretty h
                                                               :: map (fn h => Symbol.spaces (String.size s_date) ^ Holder0.pretty h) hs end)) l
      of (true, l) :: ls =>
        let fun f s_copy (l :: ls) = 
          s_copy ^ l ^ String.concat (map (fn s => "\n" ^ Symbol.spaces (String.size s_copy) ^ s) ls)
        in f s_copy l ^ String.concat (map (fn (b, l) => "\n" ^ f (s_portions b) l) ls) end
    end
end

structure Copyright = Theory_Data' (Copyright0)

structure License0 : OBJECT = struct
  type T = Input.source
  val key = "license"
  val pretty = pretty_input
end

structure License = Theory_Data' (License0)

type project_head = (Input.source * Copyright0.T) list

structure Project0 : sig include OBJECT val pretty0 : bool -> project_head * Input.source -> string
                     end = struct
  type T = project_head * License0.T
  val key = "project"
  fun wrap_stars s =
    let val stars = "******************************************************************************" in
      cat_lines
        ("(" ^ stars
         :: map ((fn s => " *" ^ s) o (fn "" => "" | s => " " ^ s)) (split_lines s)
         @ [" " ^ stars ^ ")"])
    end
  fun pretty0 stars (l, lic) =
    let val s_end = case l of [_] => "" | _ => "\n\n *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *"
    in String.concat (map (fn (src, copy) => pretty_input src ^ (if stars then "" else " " ^ Symbol.open_) ^ "\n\n" ^ Copyright0.pretty copy ^ s_end ^ (if stars then "" else " " ^ Symbol.close ^ Symbol.open_) ^ "\n\n") l)
       ^ License0.pretty lic
       |> (if stars then wrap_stars else fn s => s ^ "\n" ^ Symbol.close)
    end
  val pretty = pretty0 true
end

structure Project = Theory_Data' (Project0)

fun define0 data_map n thy = data_map (#2 o Name_Space.define (Context.Theory thy) true n) thy
fun define key data_map n =
  ( key
  , Toplevel.theory
      (fn thy => data_map (#2 o Name_Space.define (Context.Theory thy) true n)
                          thy))

local
  fun check0 f_map key data_get f n f_left =
    ( key
    , Toplevel.theory
        (fn thy => f (f_map (fn (Right a, v) => (Right a, v)
                              | (Left k, v) => (Left (f_left (Name_Space.check (Context.Theory thy) (data_get thy)) k), v)) n) thy))
in
fun check key data_get f n = check0 (fn f => Option.map (the_left o #1 o f)) key data_get f (Option.map (fn n => (Left n, ())) n)
fun check' key = check0 map key
end

structure Parse' = struct
  datatype copyright = C_ref of string * Position.T
                     | C_def of (((string option * int) * (bool * int) option) * (string * Position.T) list) list
  val copyright =
    Scan.repeat (Scan.option (Parse.$$$ "portions") -- Parse.nat -- Scan.option ((Parse.$$$ "," >> K false || Parse.minus >> K true) -- Parse.nat) -- Parse.list1 (Parse.position Parse.name))
  
  fun copyright_check key f = check' key Holder.get f
  
  fun copyright_check' h ((portions, d0), opt_d) =
                          ( portions = NONE
                          , case opt_d of SOME (true, d_max) => D_interval (d0, d_max)
                                        | SOME (false, d1) => D_discrete [d0, d1]
                                        | NONE => D_discrete [d0]
                          , h)
end

val _ =
  Outer_Syntax.commands @{command_keyword project} "formal comment (primary style)"
    (Parse.binding --| Parse.$$$ "::" -- Parse.position Parse.name -- Scan.repeat1 (Parse.where_ |-- Parse.document_source --
                 (   Parse.$$$ "imports" |-- Parse.position Parse.name >> Parse'.C_ref
                  || Parse.$$$ "defines" |-- Parse'.copyright >> Parse'.C_def)) >>
     (fn ((n, lic), l_pj) =>
       [( @{command_keyword project}
        , Toplevel.theory
            (fn thy => 
              define0
                Project.map
                ( n
                , ( map (fn (x, opt_n) =>
                          (x, case opt_n of
                                Parse'.C_ref n => #2 (Name_Space.check (Context.Theory thy) (Copyright.get thy) n)
                              | Parse'.C_def l_src => map (fn (v, holder) => Parse'.copyright_check' (map (#2 o Name_Space.check (Context.Theory thy) (Holder.get thy)) holder) v) l_src))
                        l_pj
                  , #2 (Name_Space.check (Context.Theory thy) (License.get thy) lic)))
                thy))]));

val _ =
  Outer_Syntax.commands @{command_keyword country} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.document_source >>
      (fn (n, src) =>
        [ define @{command_keyword country} Country.map (n, src)
        , (@{command_keyword country}, Thy_Output.document_command {markdown = true} (NONE, src))]));

val _ =
  Outer_Syntax.commands @{command_keyword holder} "formal comment (primary style)"
    (Parse.binding -- Scan.option (Parse.$$$ "::" |-- Parse.position Parse.name) --| Parse.where_ -- Parse.list Parse.document_source >>
      (fn ((name, country), l_src) =>
        check
          @{command_keyword holder}
          Country.get
          (fn country => define0 Holder.map (name, (l_src, Option.map #2 country)))
          country
          I
        :: map (fn src =>
                 (@{command_keyword holder}, Thy_Output.document_command {markdown = true} (NONE, src)))
               l_src));

val _ =
  Outer_Syntax.commands @{command_keyword copyright} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse'.copyright >>
      (fn (n, l_src) =>
        [Parse'.copyright_check
          @{command_keyword copyright}
          (fn l => define0
                     Copyright.map
                     (n, map (fn (Left h, d) => Parse'.copyright_check' h d) l))
          (map (fn (a, b) => (Left b, a)) l_src)
          (fn f => map (#2 o f))]));

val _ =
  Outer_Syntax.commands @{command_keyword license} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.document_source (* ignored for bootstrapping *)
                                    -- Parse.document_source >>
      (fn ((n, _), src) =>
        [ define @{command_keyword license} License.map (n, src)
        , (@{command_keyword license}, Thy_Output.document_command {markdown = true} (NONE, src))]));

val _ =
  Outer_Syntax.commands' @{command_keyword check_license} "formal comment (primary style)"
    (Scan.repeat (Parse.position Parse.name) --| Parse.$$$ "in" -- Scan.option (Parse.$$$ "file") -- Parse.position Parse.path >>
      (fn ((pj, file), loc) => fn thy => fn _ =>
        let
          fun head stars = map (fn n => Project0.pretty0 stars (#2 (Name_Space.check (Context.Theory thy) (Project.get thy) n))) pj
          val l_head = head true
          val l_head0 = head false
          (*val _ = List.app (fn s => writeln s) l_head0*)
          fun f s =
            let
              fun f_exists f_un s l = fold (fn p => fn b => b orelse try (f_un p) s <> NONE) l false
            in
              cons ( @{command_keyword check_license}
                   , Toplevel.keep
                       (fn _ =>
                         let val base_name = Path.base_name s
                         in
                           if f_exists unprefix (File.read s) (if base_name = "LICENSE.thy" then l_head0 else l_head) then
                             writeln (@{make_string} s)
                           else if f_exists unsuffix base_name [".thy", ".ml", ".ML", "ROOT"] then
                             error (@{make_string} s)
                           else
                             warning (@{make_string} s)
                         end))
            end
        in
          (case file of NONE => fold_dir f (Resources'.check_dir thy loc)
                      | SOME _ => f (Resources'.check_path' (SOME File.check_file) (Proof_Context.init_global thy) (Resources.master_directory thy) loc))
            []
        end))

val _ =
  Outer_Syntax.command @{command_keyword insert_license} "formal comment (primary style)"
    (Scan.option Parse.binding >>
      (fn _ => Toplevel.keep (fn _ => warning "to be implemented")))

val _ =
  Outer_Syntax.command @{command_keyword map_license} "formal comment (primary style)"
    (Scan.option Parse.binding >>
      (fn _ => Toplevel.keep (fn _ => warning "to be implemented")))
\<close>

end