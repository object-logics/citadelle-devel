(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
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

header{* Part ... *}

theory OCL_class_diagram_generator
imports OCL_compiler
  keywords (* ocl (USE tool) *)
           "Between" "End"
           "Attributes" "Operations" "Constraints"
           "Role"
           "Ordered" "Subsets" "Union" "Redefines" "Derived" "Qualifier"
           "Existential" "Inv" "Pre" "Post"
           (* ocl (added) *)
           "skip" "self"

           (* hol syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION"
           "deep" "shallow" "syntax_print"
           "generation_semantics"
           "flush_all"

           (* hol semantics *)
           "design" "analysis" "oid_start"

       and (* ocl (USE tool) *)
           "Abstract_class" "Class"
           "Association" "Composition" "Aggregation"
           "Abstract_associationclass" "Associationclass"
           "Context"
           (* ocl (added) *)
           "Class.end" "Instance" "Define_int" "Define_state" "Define_pre_post"

           (* hol syntax *)
           "generation_syntax"

           :: thy_decl
begin

section{* Generation to Shallow Form: SML *}

subsection{* global *}

apply_code_printing_reflect {*
  (* this variable is not used but needed for well typechecking the reflected SML code *)
  val stdout_file = Unsynchronized.ref ""
*}
code_reflect OCL
   functions (* OCL compiler as monadic combinators for deep and shallow *)
             fold_thy_deep fold_thy_shallow

             (* printing the HOL AST to (shallow Isabelle) string *)
             write_file

             (* manipulating the compiling environment *)
             ocl_compiler_config_reset_all oidInit D_file_out_path_dep_update

             (* printing the OCL AST to (deep Isabelle) string *)
             i_apply i_of_ocl_compiler_config i_of_ocl_deep_embed_ast

ML{*
 val To_string = implode o map str
 fun To_nat (Code_Numeral.Nat i) = i
*}

ML{*
structure From = struct
 open OCL
 val from_char = I
 val from_string = String.explode
 val from_binding = from_string o Binding.name_of
 fun from_term ctxt s = from_string (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt s)))
 val from_nat = Code_Numeral.Nat
 val from_internal_oid = Oid
 val from_bool = I
 val from_unit = I
 val from_option = Option.map
 val from_list = List.map
 fun from_pair f1 f2 (x, y) = (f1 x, f2 y)
 val from_design_analysis = fn NONE => Gen_design | _ => Gen_analysis
end
*}

ML{*
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global
*}

ML{* fun List_mapi f = OCL.list_mapi (f o To_nat) *}

subsection{* General Compiling Process: Deep (with reflection) *}

ML{*
structure Deep0 = struct

fun apply_hs_code_identifiers ml_module thy =
  let fun mod_hs (fic, ml_module) = Code_Symbol.Module (fic, [("Haskell", SOME ml_module)]) in
  fold (Code_Target.set_identifiers o mod_hs)
    [ ( case Properties.get (snd (Theory.get_markup thy)) "name" of
                 SOME s => s
      , ml_module)
    , ("OCL_compiler", ml_module)
    , ("OCL_compiler_ast", ml_module)] thy end

val gen_empty = ""

structure Export_code_env = struct
  structure Isabelle = struct
    val function = "write_file"
    val argument_main = "main"
  end

  structure Haskell = struct
    val function = "Function"
    val argument = "Argument"
    val main = "Main"
    structure Filename = struct
      fun hs_function ext = function ^ "." ^ ext
      fun hs_argument ext = argument ^ "." ^ ext
      fun hs_main ext = main ^ "." ^ ext
    end
  end

  structure OCaml = struct
    val make = "write"
    structure Filename = struct
      fun function ext = "function." ^ ext
      fun argument ext = "argument." ^ ext
      fun main_fic ext = "main." ^ ext
      fun makefile ext = make ^ "." ^ ext
    end
  end

  structure Scala = struct
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
    end
  end

  structure SML = struct
    val main = "Run"
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
      fun stdout ext = "Stdout." ^ ext
      fun main_fic ext = main ^ "." ^ ext
    end
  end

  datatype file_input = File
                      | Directory
end

fun compile l cmd =
  let val (l, rc) = fold (fn cmd => (fn (l, 0) =>
                                         let val {out, err, rc, ...} = Bash.process cmd in
                                         ((out, err) :: l, rc) end
                                     | x => x)) l ([], 0)
      val l = rev l in
  if rc = 0 then
    (l, Isabelle_System.bash_output cmd)
  else
    let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
    error "Compilation failed"
    end
  end

fun check l () =
  fold (fn (cmd, msg) => fn () =>
    let val (out, rc) = Isabelle_System.bash_output cmd in
    if rc = 0 then
      ()
    else
      ( writeln out
      ; error msg)
    end) l ()

val compiler = let open Export_code_env in
  [ let val ml_ext = "hs" in
    ( "Haskell", ml_ext, Directory, Haskell.Filename.hs_function
    , check [("ghc --version", "ghc is not installed (required for compiling a Haskell project)")]
    , (fn mk_fic => fn ml_module => fn mk_free => fn thy =>
        File.write (mk_fic ("Main." ^ ml_ext))
          (String.concatWith "; " [ "import qualified Unsafe.Coerce"
                         , "import qualified " ^ Haskell.function
                         , "import qualified " ^ Haskell.argument
                         , "main :: IO ()"
                         , "main = " ^ Haskell.function ^ "." ^ Isabelle.function ^ " (Unsafe.Coerce.unsafeCoerce " ^ Haskell.argument ^ "." ^
                           mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^
                           ")"]))
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ "/" ^ Haskell.Filename.hs_argument ml_ext ^ " " ^ Path.implode tmp_export_code
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ghc -outputdir _build " ^ Haskell.Filename.hs_main ml_ext ]
                (Path.implode (Path.append tmp_export_code (Path.make [Haskell.main]))))
    end
  , let val ml_ext = "ml" in
    ( "OCaml", ml_ext, File, OCaml.Filename.function
    , check [("ocp-build -version", "ocp-build is not installed (required for compiling an OCaml project)")
            ,("ocamlopt -version", "ocamlopt is not installed (required for compiling an OCaml project)")]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val () = File.write (mk_fic (OCaml.Filename.makefile "ocp"))
                              (String.concat [ "comp += \"-g\" link += \"-g\" "
                                             , "begin generated = true begin library \"nums\" end end "
                                             , "begin program \"", OCaml.make, "\" sort = true files = [ \"", OCaml.Filename.function ml_ext
                                             , "\" \"", OCaml.Filename.argument ml_ext
                                             , "\" \"", OCaml.Filename.main_fic ml_ext
                                             , "\" ]"
                                             , "requires = [\"nums\"] "
                                             , "end" ]) in
         File.write (mk_fic (OCaml.Filename.main_fic ml_ext))
           ("let _ = Function." ^ ml_module ^ "." ^ Isabelle.function ^ " (Obj.magic (Argument." ^ ml_module ^ "." ^
            mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^ "))")
         end
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [OCaml.Filename.argument ml_ext]))
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ocp-build -init -scan -no-bytecode 2>&1" ]
                (Path.implode (Path.append tmp_export_code (Path.make [ "_obuild", OCaml.make, OCaml.make ^ ".asm"]))))
    end
  , let val ml_ext = "scala"
        val ml_module = Unsynchronized.ref ("", "") in
    ( "Scala", ml_ext, File, Scala.Filename.function
    , check [("scala -e 0", "scala is not installed (required for compiling a Scala project)")]
    , (fn _ => fn ml_mod => fn mk_free => fn thy => 
        ml_module := (ml_mod, mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list)))
    , fn tmp_export_code => fn tmp_file =>
        let val l = File.read_lines (Path.explode tmp_file)
            val (ml_module, ml_main) = Unsynchronized.! ml_module
            val () = File.write_list
                       (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext]))
                       (List.map
                         (fn s => s ^ "\n")
                         ("object " ^ ml_module ^ " { def main (__ : Array [String]) = " ^ ml_module ^ "." ^ Isabelle.function ^ " (" ^ ml_module ^ "." ^ ml_main ^ ")" :: l @ ["}"])) in
        compile []
                ("scala -nowarn " ^ Path.implode (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext])))
        end)
    end
  , let val ml_ext_thy = "thy"
        val ml_ext_ml = "ML" in
    ( "SML", ml_ext_ml, File, SML.Filename.function
    , check [ let val isa = "isabelle" in
              ( Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", isa]))) ^ " version"
              , isa ^ " is not installed (required for compiling a SML project)")
              end ]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val esc_star = "*"
             val esc_accol1 = "{" ^ esc_star
             val esc_accol2 = esc_star ^ "}" in
         File.write_list (mk_fic (SML.Filename.main_fic ml_ext_thy))
           (map (fn s => s ^ "\n") (List.concat
           [ [ "theory " ^ SML.main
             , "imports Main"
             , "begin"
             , "ML" ^ esc_accol1]
           , map (fn s => s ^ ";")
             let val arg = "argument" in
             [ "val stdout_file = Unsynchronized.ref (File.read (Path.make [\"" ^ SML.Filename.stdout ml_ext_ml ^ "\"]))"
             , "print_depth 100" (* any large number so that @{make_string} displays all the expression *)
             , "use \"" ^ SML.Filename.argument ml_ext_ml ^ "\""
             , "val " ^ arg ^ " = XML.content_of (YXML.parse_body (@{make_string} (" ^ ml_module ^ "." ^
               mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^ ")))"
             , "use \"" ^ SML.Filename.function ml_ext_ml ^ "\""
             , "ML_Context.eval_text false Position.none (\"let open " ^ ml_module ^ " " ^ Isabelle.function ^ " (\" ^ " ^ arg ^ " ^ \") end\")" ]
             end
           , [ esc_accol2
             , "end"] ]))
         end
    , fn tmp_export_code => fn tmp_file => 
        let val stdout_file = Isabelle_System.create_tmp_path "stdout_file" "thy"
            val () = File.write (Path.append tmp_export_code (Path.make [SML.Filename.stdout ml_ext_ml])) (Path.implode (Path.expand stdout_file))
            val (l, (_, exit_st)) = 
              compile [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [SML.Filename.argument ml_ext_ml]))
                      , "cd " ^ Path.implode tmp_export_code ^
                        " && cat " ^ SML.Filename.main_fic ml_ext_thy ^
                        " | " ^
                        Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", "isabelle"]))) ^ " tty" ]
                      "true"
            val stdout = 
              case SOME (File.read stdout_file) handle _ => NONE of
                SOME s => let val () = File.rm stdout_file in s end
              | NONE => "" in
            (l, (stdout, if List.exists (fn (err, _) =>
                              List.exists (fn "*** Error" => true | _ => false)
                                (String.tokens (fn #"\n" => true | _ => false) err)) l then
                           let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
                           1
                           end
                         else exit_st))
        end)
    end ]
end

fun find_ext ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, ext, _, _, _, _, _) => ext

fun find_export_mode ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, mode, _, _, _, _) => mode

fun find_function ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, f, _, _, _) => f

fun find_check_compil ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, build, _, _) => build

fun find_init ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, build, _) => build

fun find_build ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, _, build) => build


end
*}

ML{*
structure Deep = struct

fun prep_destination "" = NONE
  | prep_destination "-" = (legacy_feature "drop \"file\" argument entirely instead of \"-\""; NONE)
  | prep_destination s = SOME (Path.explode s)

fun produce_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs in
    map (fn (((target, module_name), some_path), args) =>
      (some_path, Code_Target.produce_code_for thy (*some_path*) target NONE module_name args naming program names_cs)) seris
  end

fun absolute_path filename thy = Path.implode (Path.append (Thy_Load.master_directory thy) (Path.explode filename))

fun export_code_cmd_gen raw_cs thy seris =
  Code_Target.export_code
                  thy
                  (Code_Target.read_const_exprs thy raw_cs)
                  ((map o apfst o apsnd) prep_destination seris)

fun export_code_tmp_file seris g =
  fold
    (fn ((ml_compiler, ml_module), export_arg) => fn f => fn g =>
      f (fn accu =>
        let val tmp_name = "OCL_class_diagram_generator" in
        (if Deep0.find_export_mode ml_compiler = Deep0.Export_code_env.Directory then
           Isabelle_System.with_tmp_dir tmp_name
         else
           Isabelle_System.with_tmp_file tmp_name (Deep0.find_ext ml_compiler))
          (fn filename =>
             g (((((ml_compiler, ml_module), Path.implode filename), export_arg) :: accu)))
        end))
    seris
    (fn f => f [])
    (g o rev)

fun mk_path_export_code tmp_export_code ml_compiler i =
  Path.append tmp_export_code (Path.make [ml_compiler ^ Int.toString i])

fun export_code_cmd' seris tmp_export_code f_err filename_thy raw_cs thy =
  export_code_tmp_file seris
    (fn seris =>
      let val mem_scala = List.exists (fn ((("Scala", _), _), _) => true | _ => false) seris
          val _ = export_code_cmd_gen
        (if mem_scala then Deep0.Export_code_env.Isabelle.function :: raw_cs else raw_cs)
        (let val v = Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.argument thy in
         if mem_scala then Code_printing.apply_code_printing v else v end)
        seris in
      List_mapi
        (fn i => fn seri => case seri of (((ml_compiler, _), filename), _) =>
          let val (l, (out, err)) =
                Deep0.find_build
                  ml_compiler
                  (mk_path_export_code tmp_export_code ml_compiler i)
                  filename
              val _ = f_err seri err in
          (l, out)
          end) seris
      end)

fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (Outer_Syntax.scan Position.none s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

val list_all_eq = fn x0 :: xs =>
  List.all (fn x1 => x0 = x1) xs

end
*}

subsection{* ... *}

ML{*
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun parse_l1' f = Parse.$$$ "[" |-- Parse.list1 f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
*}

ML{*
structure Generation_mode = struct
datatype 'a generation_mode = Gen_deep of unit OCL.ocl_compiler_config_ext
                                        * (string * string list) option
                                        * ((bstring (* compiler *) * bstring (* main module *) ) * Token.T list) list (* seri_args *)
                                        * bstring option (* filename_thy *)
                                        * Path.T (* tmp dir export_code *)
                            | Gen_shallow of unit OCL.ocl_compiler_config_ext
                                           * 'a (* theory init *)
                            | Gen_syntax_print

structure Data_gen = Theory_Data
  (type T = theory generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) []

val parse_scheme = @{keyword "design"} >> K NONE || @{keyword "analysis"} >> K (SOME 1)

val parse_deep =
     Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")" -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- parse_l' Parse.name) --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- (* code_expr_inP *) parse_l1' (@{keyword "in"} |-- (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME) NONE

val parse_sem_ocl =
      (Parse.$$$ "(" -- @{keyword "generation_semantics"} -- Parse.$$$ "[")
  |-- parse_scheme -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat) 0
  --| (Parse.$$$ "]" -- Parse.$$$ ")")

val mode =
  let fun mk_ocl disable_thy_output file_out_path_dep oid_start design_analysis =
    OCL.ocl_compiler_config_empty
                    (From.from_bool disable_thy_output)
                    (From.from_option (From.from_pair From.from_string (From.from_list From.from_string)) file_out_path_dep)
                    (OCL.oidInit (From.from_internal_oid (From.from_nat oid_start)))
                    (From.from_design_analysis design_analysis) in

     @{keyword "deep"} |-- parse_sem_ocl -- parse_deep >> (fn ((design_analysis, oid_start), (((file_out_path_dep, disable_thy_output), seri_args), filename_thy)) =>
       Gen_deep ( mk_ocl (not disable_thy_output) file_out_path_dep oid_start design_analysis
                , file_out_path_dep, seri_args, filename_thy, Isabelle_System.create_tmp_path "deep_export_code" ""))
  || @{keyword "shallow"} |-- parse_sem_ocl >> (fn (design_analysis, oid_start) =>
       Gen_shallow (mk_ocl true NONE oid_start design_analysis, ()))
  || @{keyword "syntax_print"} >> K Gen_syntax_print
  end


fun f_command l_mode =
      Toplevel.theory (fn thy =>
        let val (l_mode, thy) = OCL.fold_list
          (fn Gen_shallow (ocl, ()) => let val thy0 = thy in
                                       fn thy => (Gen_shallow (ocl, thy0), thy) end
            | Gen_syntax_print => (fn thy => (Gen_syntax_print, thy))
            | Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code) => fn thy =>
                let val _ = warning ("remove the directory (at the end): " ^ Path.implode tmp_export_code)
                    val seri_args' = List_mapi (fn i => fn ((ml_compiler, ml_module), export_arg) =>
                      let val tmp_export_code = Deep.mk_path_export_code tmp_export_code ml_compiler i
                          fun mk_fic s = Path.append tmp_export_code (Path.make [s])
                          val () = Deep0.find_check_compil ml_compiler ()
                          val () = Isabelle_System.mkdirs tmp_export_code in
                      ((( (ml_compiler, ml_module)
                        , Path.implode (if Deep0.find_export_mode ml_compiler = Deep0.Export_code_env.Directory then
                                          tmp_export_code
                                        else
                                          mk_fic (Deep0.find_function ml_compiler (Deep0.find_ext ml_compiler))))
                        , export_arg), mk_fic)
                      end) seri_args
                    val _ = Deep.export_code_cmd_gen
                              [Deep0.Export_code_env.Isabelle.function]
                              (Code_printing.apply_code_printing (Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.function thy))
                              (List.map fst seri_args')
                    val () = fold (fn ((((ml_compiler, ml_module), _), _), mk_fic) => fn _ =>
                      Deep0.find_init ml_compiler mk_fic ml_module Deep.mk_free thy) seri_args' () in
                (Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code), thy) end) l_mode thy in
        Data_gen.map (Symtab.map_default (Deep0.gen_empty, l_mode) (fn _ => l_mode)) thy
        end)
end
*}

subsection{* General Compiling Process: Shallow *}

ML{*
structure OCL_overload = struct
  val s_of_rawty = OCL.s_of_rawty To_string
  val s_of_expr = OCL.s_of_expr To_string (Int.toString o To_nat)
  val s_of_sexpr = OCL.s_of_sexpr To_string (Int.toString o To_nat)
  val fold = fold
end
*}

ML{*
structure Shallow_conv = struct
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_ntheorem ctxt s = let open OCL open OCL_overload in case s of
    Thm_str s => Proof_Context.get_thm ctxt (To_string s)
  | Thm_THEN (e1, e2) => m_of_ntheorem ctxt e1 RSN (1, m_of_ntheorem ctxt e2)
  | Thm_simplified (e1, e2) => asm_full_simplify (clear_simpset ctxt addsimps [m_of_ntheorem ctxt e2]) (m_of_ntheorem ctxt e1)
  | Thm_OF (e1, e2) => [m_of_ntheorem ctxt e2] MRS m_of_ntheorem ctxt e1
  | Thm_where (nth, l) => read_instantiate ctxt (List.map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (m_of_ntheorem ctxt nth)
  | Thm_symmetric s => m_of_ntheorem ctxt (Thm_THEN (s, Thm_str (From.from_string "sym")))
  | Thm_of (nth, l) =>
      let val thm = m_of_ntheorem ctxt nth
          fun zip_vars _ [] = []
            | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
            | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
            | zip_vars [] _ = error "More instantiations than variables in theorem" in
      read_instantiate ctxt (List.map (fn (v, expr) => (v, s_of_expr expr))
                                 (zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) []))
                                           (List.map SOME l))) thm
      end
end

fun m_of_tactic expr = let open OCL open Method open OCL_overload in case expr of
    Tac_rule s => Basic (fn ctxt => rule [m_of_ntheorem ctxt s])
  | Tac_drule s => Basic (fn ctxt => drule 0 [m_of_ntheorem ctxt s])
  | Tac_erule s => Basic (fn ctxt => erule 0 [m_of_ntheorem ctxt s])
  | Tac_elim s => Basic (fn ctxt => elim [m_of_ntheorem ctxt s])
  | Tac_intro l => Basic (fn ctxt => intro (map (m_of_ntheorem ctxt) l))
  | Tac_subst_l (l, s) => Basic (fn ctxt => SIMPLE_METHOD' (EqSubst.eqsubst_tac ctxt (map (fn s => case Int.fromString (To_string s) of SOME i => i) l) [m_of_ntheorem ctxt s]))
  | Tac_insert l => Basic (fn ctxt => insert (List.map (m_of_ntheorem ctxt) l))
  | Tac_plus t => Repeat1 (Then (List.map m_of_tactic t))
  | Tac_option t => Try (Then (List.map m_of_tactic t))
  | Tac_blast n => Basic (case n of NONE => SIMPLE_METHOD' o blast_tac
                                  | SOME lim => fn ctxt => SIMPLE_METHOD' (depth_tac ctxt (To_nat lim)))
  | Tac_simp => simp_tac I
  | Tac_simp_add l => simp_tac (fn ctxt => ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_add0 l => simp_tac (fn ctxt => ctxt addsimps (List.map (m_of_ntheorem ctxt) l))
  | Tac_simp_add_del (l_add, l_del) => simp_tac (fn ctxt => ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l_add)
                                                                 delsimps (List.map (Proof_Context.get_thm ctxt o To_string) l_del))
  | Tac_simp_only l => simp_tac (fn ctxt => clear_simpset ctxt addsimps (List.map (m_of_ntheorem ctxt) l))
  | Tac_simp_all => m_of_tactic (Tac_plus [Tac_simp])
  | Tac_simp_all_add s => m_of_tactic (Tac_plus [Tac_simp_add [s]])
  | Tac_auto_simp_add l => Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l))))
  | Tac_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (fold (fn (f, l) => fold f l)
              [(Simplifier.add_simp, List.map (m_of_ntheorem ctxt) l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string) l_split)]
              ctxt)))
  | Tac_rename_tac l => Basic (K (SIMPLE_METHOD' (rename_tac (List.map To_string l))))
  | Tac_case_tac e => Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (s_of_expr e)))
end

end

structure Shallow_ml = struct open Shallow_conv
fun perform_instantiation thy tycos vs f_eq add_def tac (*add_eq_thms*) =
    thy
    |> Class.instantiation (tycos, vs, f_eq)
    |> fold_map add_def tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn _ => tac)
(*    |-> fold Code.del_eqn
    |> fold add_eq_thms tycos*)
    |-> K I
local
fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if null ignored then ()
      else Context_Position.if_visible ctxt warning
        ("Ignoring sort constraints in type variables(s): " ^
          commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
          "\nin type abbreviation " ^ (case b of NONE => "" | SOME b => Binding.print b));
  in rhs end
in
fun read_typ_syntax b = read_abbrev b
                      o Proof_Context.init_global
end

fun then_tactic l = (Method.Then (map m_of_tactic l), (Position.none, Position.none))

fun local_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.local_done_proof
 | Tacl_sorry => Proof.local_skip_proof true
 | Tacl_by l_apply => Proof.local_terminal_proof (then_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.global_done_proof
 | Tacl_sorry => Proof.global_skip_proof true
 | Tacl_by l_apply => Proof.global_terminal_proof (then_tactic l_apply, NONE)
end

fun proof_show f st = st
  |> Proof.enter_forward
  |> f
  |> Isar_Cmd.show [((@{binding ""}, []), [("?thesis", [])])] true

val apply_results = let open OCL_overload in fn OCL.App l => (fn st => st |> (Proof.apply_results (then_tactic l)) |> Seq.the_result "")
                     | OCL.App_using l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.using [map (fn s => ([m_of_ntheorem ctxt s], [])) l] st
                         end)
                     | OCL.App_unfolding l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.unfolding [map (fn s => ([m_of_ntheorem ctxt s], [])) l] st
                         end)
                     | OCL.App_let (e1, e2) => proof_show (Proof.let_bind_cmd [([s_of_expr e1], s_of_expr e2)])
                     | OCL.App_have (n, e, e_pr) => proof_show (fn st => st
                         |> Isar_Cmd.have [((To_sbinding n, []), [(s_of_expr e, [])])] true
                         |> local_terminal_proof e_pr)
                     | OCL.App_fix l => proof_show (Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l))
end

end

structure Shallow_main = struct open Shallow_conv open Shallow_ml
val OCL_main = let open OCL open OCL_overload in (*let val f = *)fn
  Theory_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       List.map (fn (n, l) => (To_sbinding n, List.map (fn OCL.Opt o_ => To_string o_ ^ " option"
                                             |   Raw o_ => To_string o_) l, NoSyn)) l)]
| Theory_ty_synonym (Type_synonym (n, l)) =>
    (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, [], NoSyn)
                                   (read_typ_syntax (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Theory_instantiation_class (Instantiation (n, n_def, expr)) =>
    (fn thy =>
     let val name = To_string n in
     perform_instantiation
       thy
       [ let val Type (s, _) = (read_typ_syntax NONE thy name) in s end ]
       []
       (Syntax.read_sort (Proof_Context.init_global thy) "object")
       (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
           (NONE, ((To_binding (To_string n_def ^ "_" ^ name ^ "_def"), []), s_of_expr expr)) false thy in
         (ty, thy)
        end)
       (fn thms => Class.intro_classes_tac [] THEN ALLGOALS (Proof_Context.fact_tac thms))
     end)
| Theory_defs_overloaded (Defs_overloaded (n, e)) =>
    Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])])
| Theory_consts_class (Consts_raw (n, ty, symb)) =>
    Sign.add_consts [( To_sbinding n
                     , s_of_rawty ty
                     , Mixfix ("(_) " ^ To_string symb, [], 1000))]
| Theory_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e)
      | Definition_abbrev0 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(" ^ s_of_expr abbrev ^ ")", [], 1000)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Theory_lemmas_simp (Lemmas_simp (s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (Attrib.intern_src (Proof_Context.theory_of lthy))
                          [Args.src (("simp", []), Position.none), Args.src (("code_unfold", []), Position.none)]),
        List.map (fn x => ([m_of_ntheorem lthy x], [])) l)]
      []
      false) lthy)
| Theory_lemmas_simp (Lemmas_simps (s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (Attrib.intern_src (Proof_Context.theory_of lthy))
                          [Args.src (("simp", []), Position.none), Args.src (("code_unfold", []), Position.none)]),
        List.map (fn x => (Proof_Context.get_thms lthy (To_string x), [])) l)]
      []
      false) lthy)
| Theory_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (" " ^ (To_string OCL.unicode_Longrightarrow) ^ " ")
                                                             (List.map s_of_expr l_spec)), [])])])
             false lthy
        |> fold (apply_results o OCL.App) l_apply
        |> global_terminal_proof o_by)
| Theory_lemma_by (Lemma_by_assum (n, l_spec, concl, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (To_sbinding n, [])
             []
             (List.map (fn (n, (b, e)) => Element.Assumes [((To_sbinding n, if b then [Args.src (("simp", []), Position.none)] else []), [(s_of_expr e, [])])]) l_spec)
             (Element.Shows [((@{binding ""}, []),[(s_of_expr concl, [])])])
             false lthy
        |> fold apply_results l_apply
        |> (case filter (fn OCL.App_let _ => true | OCL.App_have _ => true | OCL.App_fix _ => true | _ => false) l_apply of
              [] => global_terminal_proof o_by
            | _ :: l => let val arg = (NONE, true) in fn st => st
              |> local_terminal_proof o_by
              |> fold (K (Proof.local_qed arg)) l
              |> Proof.global_qed arg end))
| Theory_axiom (Axiom (n, e)) => #2 o Specification.axiomatization_cmd
                                     []
                                     [((To_sbinding n, []), [s_of_expr e])]
| Theory_section_title _ => I
| Theory_text _ => I
| Theory_ml ml => Code_printing.reflect_ml (case ml of Ml ml => s_of_sexpr ml)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end
end
(*val _ = print_depth 100*)
*}

subsection{* ... *}

ML{*

fun exec_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, l_obj) thy0 =
  let open Generation_mode in
  let val i_of_arg =
    let val a = OCL.i_apply
      ; val b = I in
    OCL.i_of_ocl_compiler_config a b (fn a => fn b =>
      OCL.i_of_pair a b
        (OCL.i_of_list a b (OCL.i_of_ocl_deep_embed_ast a b))
        (OCL.i_of_option a b (OCL.i_of_string a b)))
    end in
  let fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
  let val name_main = Deep.mk_free (Proof_Context.init_global thy0) Deep0.Export_code_env.Isabelle.argument_main [] in
  thy0 |> def (String.concatWith " " (  name_main
                                    :: "="
                                    :: To_string (i_of_arg (OCL.ocl_compiler_config_more_map (fn () => (l_obj, From.from_option From.from_string (Option.map (fn filename_thy => Deep.absolute_path filename_thy thy0) filename_thy))) ocl))
                                    :: []))
       |> Deep.export_code_cmd' seri_args tmp_export_code
            (fn (((_, _), msg), _) => fn err => if err <> 0 then error msg else ()) filename_thy [name_main]
       |> (fn l =>
             let val (l_warn, l) = (map fst l, map snd l) in
             if Deep.list_all_eq l then (List.concat l_warn, hd l) else error "There is an extracted language which does not produce a similar Isabelle content as the others"
             end)
       |> (fn (l_warn, s) =>
             let val () = writeln
               (case (file_out_path_dep, filename_thy) of
                  (SOME _, SOME _) => s
                | _ => String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                   (String.tokens (fn c => From.from_char c = OCL.char_escape) s))) in
             fold (fn (out, err) => K ( writeln (Markup.markup Markup.keyword2 err)
                                      ; case trim_line out of
                                          "" => ()
                                        | out => writeln (Markup.markup Markup.keyword1 out))) l_warn () end)

end end end end

fun outer_syntax_command mk_string cmd_spec cmd_descr parser get_oclclass =
  let open Generation_mode in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (ocl, thy) =
        OCL.fold_list

          let val get_oclclass = get_oclclass name in
          fn Gen_syntax_print => (fn thy => let val _ = writeln (mk_string name) in (Gen_syntax_print, thy) end)
           | Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code) =>
              (fn thy0 =>
                let val obj = get_oclclass thy0
                  ; val l_obj = [obj] in
                thy0 |> exec_deep (OCL.d_file_out_path_dep_update (fn _ => NONE) ocl, file_out_path_dep, seri_args, NONE, tmp_export_code, l_obj)
                     |> K (Gen_deep (OCL.fold_thy_deep l_obj ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code), thy0)
                end)
           | Gen_shallow (ocl, thy0) => fn thy =>
             let val (ocl, thy) = OCL.fold_thy_shallow
                   (fn f => f () handle ERROR e =>
                     ( warning "Shallow Backtracking: HOL declarations occuring among OCL ones are ignored (if any)"
                       (* TODO automatically determine if there is such HOL declarations,
                               for raising earlier a specific error message *)
                     ; error e))
                   (fn _ => fn _ => thy0)
                   Shallow_main.OCL_main
                   [get_oclclass thy]
                   (ocl, thy) in
             (Gen_shallow (ocl, thy0), thy)
             end
          end

          (case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => [Gen_syntax_print])
          thy
        in
        Data_gen.map (Symtab.update (Deep0.gen_empty, ocl)) thy end)))
end
*}

subsection{* ... *}

ML{*
val () = let open Generation_mode in
  Outer_Syntax.command @{command_spec "generation_syntax"} "set the generating list"
    ((   parse_l' mode >> SOME
     || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => f_command x
      | NONE =>
      Toplevel.theory (fn thy =>
        let val l = case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => []
            val l = List.concat (List.map (fn Gen_deep x => [x] | _ => []) l)
            val _ = case l of [] => warning "Nothing to perform." | _ => ()
            val thy =
        fold
          (fn (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code) => fn thy0 =>
                thy0 |> let val (ocl, l_exec) = OCL.ocl_compiler_config_reset_all ocl in
                        exec_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, l_exec) end
                     |> K thy0)
          l
          thy
        in
        thy end)))
end
*}

subsection{* ... *}

ML{*
structure USE_parse = struct
 fun optional f = Scan.optional (f >> SOME) NONE
 val colon = Parse.$$$ ":"
 fun repeat2 scan = scan ::: Scan.repeat1 scan
 (* *)
 datatype use_oclty = OclTypeBoolean
                    | OclTypeInteger
                    | OclTypeSet of use_oclty
                    | OclTypeSequence of use_oclty
                    | OclTypeRaw of binding (* FIXME use 'string' and Parse.typ *)

 datatype use_opt = Ordered | Subsets of binding | Union | Redefines of binding | Derived of string | Qualifier of (binding * use_oclty) list
 datatype use_operation_def = Expression of string | BlockStat

 fun from_oclty v = (fn OclTypeBoolean    => OCL.OclTy_boolean
                      | OclTypeInteger    => OCL.OclTy_integer
                      | OclTypeSet l      => OCL.OclTy_collection (OCL.Set, from_oclty l)
                      | OclTypeSequence l => OCL.OclTy_collection (OCL.Sequence, from_oclty l)
                      | OclTypeRaw s      => OCL.OclTy_raw (From.from_binding s)) v

 val ident_dot_dot = Parse.alt_string (* ".." *)
 val ident_star = Parse.alt_string (* "*" *)
 (* *)
 fun use_type v = (Parse.reserved "Set" |-- Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> OclTypeSet
                || Parse.reserved "Sequence" |-- Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> OclTypeSequence
                || Parse.reserved "Boolean" >> K OclTypeBoolean
                || Parse.reserved "Integer" >> K OclTypeInteger
                || Parse.binding >> OclTypeRaw) v

 val use_expression = Parse.alt_string
 val use_variableDeclaration = Parse.binding --| Parse.$$$ ":" -- use_type
 val use_paramList = Parse.$$$ "(" |-- Parse.list use_variableDeclaration --| Parse.$$$ ")"
 val use_multiplicitySpec = ident_star || Parse.number
 val use_multiplicity = use_multiplicitySpec -- optional (ident_dot_dot |-- use_multiplicitySpec)
 val use_associationEnd =
      Parse.binding
   -- parse_l1' use_multiplicity
   -- optional (@{keyword "Role"} |-- Parse.binding)
   -- Scan.repeat (   @{keyword "Ordered"} >> K Ordered
                   || @{keyword "Subsets"} |-- Parse.binding >> Subsets
                   || @{keyword "Union"} >> K Union
                   || @{keyword "Redefines"} |-- Parse.binding >> Redefines
                   || @{keyword "Derived"} -- Parse.$$$ "=" |-- use_expression >> Derived
                   || @{keyword "Qualifier"} |-- use_paramList >> Qualifier)
   --| optional Parse.semicolon
 val use_blockStat = Parse.alt_string
 val use_prePostClause =
      (@{keyword "Pre"} || @{keyword "Post"})
   -- optional Parse.binding
   --| colon
   -- use_expression
 val use_invariantClause = Scan.optional (@{keyword "Existential"} >> K true) false
   --| @{keyword "Inv"}
   -- Parse.binding
   --| colon
   -- use_expression
 (* *)
 val class_def_list = Scan.optional (Parse.$$$ "<" |-- Parse.list1 Parse.binding) []
 val class_def_attr = Scan.optional (@{keyword "Attributes"}
   |-- Scan.repeat (Parse.binding --| colon -- use_type)
   --| optional Parse.semicolon) []
 val class_def_oper = optional (@{keyword "Operations"}
   |-- Parse.binding
   -- use_paramList
   -- optional (colon -- use_type)
   -- optional (Parse.$$$ "=" |-- use_expression || use_blockStat)
   -- Scan.repeat use_prePostClause
   --| optional Parse.semicolon)
 val class_def_constr = optional (@{keyword "Constraints"}
   |-- use_invariantClause)
end
*}

subsection{* Outer Syntax: (abstract) class *}

ML{*
datatype use_classDefinition = USE_class | USE_class_abstract

structure Outer_syntax_Class = struct
  fun make binding child attribute =
    (OCL.Ocl_class_raw_ext
         ( From.from_binding binding
         , From.from_list (From.from_pair From.from_binding USE_parse.from_oclty) attribute
         , case child of [] => NONE | [x] => SOME (From.from_binding x)
         , From.from_unit ()))
end

local
 open USE_parse

 fun mk_classDefinition _ cmd_spec =
   outer_syntax_command @{make_string} cmd_spec "Class generation"
    (   Parse.binding
     -- class_def_list
     -- class_def_attr
     -- class_def_oper
     -- class_def_constr
     --| @{keyword "End"})
    (fn ((((binding, child), attribute), _), _) => fn _ =>
       OCL.OclAstClassRaw (Outer_syntax_Class.make binding child attribute))
in
val () = mk_classDefinition USE_class @{command_spec "Class"}
val () = mk_classDefinition USE_class_abstract @{command_spec "Abstract_class"}
end
*}

subsection{* Outer Syntax: association, composition, aggregation *}

ML{*
structure Outer_syntax_Association = struct
  val mk_mult = fn "*" => OCL.Mult_star
                 | s => OCL.Mult_nat (case Int.fromString s of SOME i => From.from_nat i)

  fun make ass_ty l =
    OCL.Ocl_association_ext
        ( ass_ty
        , List.map (fn (((cl_from, cl_mult), o_cl_attr), _) =>
            (From.from_binding cl_from, (OCL.OclMult (List.map (From.from_pair mk_mult (From.from_option mk_mult)) cl_mult), From.from_option From.from_binding o_cl_attr))) l
        , From.from_unit ())
end

local
 open USE_parse

 fun mk_associationDefinition ass_ty cmd_spec =
  outer_syntax_command @{make_string} cmd_spec ""
    (    Parse.binding
     --| @{keyword "Between"}
     -- repeat2 use_associationEnd
     --| @{keyword "End"})
    (fn (_, l) => fn _ =>
      OCL.OclAstAssociation (Outer_syntax_Association.make ass_ty l))
in
val () = mk_associationDefinition OCL.OclAssTy_association @{command_spec "Association"}
val () = mk_associationDefinition OCL.OclAssTy_composition @{command_spec "Composition"}
val () = mk_associationDefinition OCL.OclAssTy_aggregation @{command_spec "Aggregation"}
end
*}

subsection{* Outer Syntax: (abstract) associationclass *}

ML{*
datatype use_associationClassDefinition = USE_associationclass | USE_associationclass_abstract

local
 open USE_parse

 fun mk_associationClassDefinition f cmd_spec =
  outer_syntax_command @{make_string} cmd_spec ""
    (   Parse.binding
     -- class_def_list
     -- (Scan.optional (@{keyword "Between"}
                        |-- repeat2 use_associationEnd >> SOME) NONE)
     -- class_def_attr
     -- class_def_oper
     -- class_def_constr
     -- optional Parse.alt_string
     --| @{keyword "End"})
    (fn ((((((binding, child), o_l), attribute), _), _), _) => fn _ =>
      OCL.OclAstAssClass (OCL.OclAssClass ( Outer_syntax_Association.make OCL.OclAssTy_association (case o_l of NONE => [] | SOME l => l)
                                          , Outer_syntax_Class.make binding child attribute)))
in
val () = mk_associationClassDefinition USE_associationclass @{command_spec "Associationclass"}
val () = mk_associationClassDefinition USE_associationclass_abstract @{command_spec "Abstract_associationclass"}
end
*}

subsection{* Outer Syntax: context *}

ML{*
datatype ('a, 'b) use_context = USE_context_invariant of 'a
                              | USE_context_pre_post of 'b
local
 open USE_parse
in
val () =
  outer_syntax_command @{make_string} @{command_spec "Context"} ""
    (
    ((* use_prePost *)
         Parse.binding
     --| Parse.$$$ "::"
     -- Parse.binding
     -- use_paramList
     -- optional (Parse.$$$ ":" |-- use_type)
     -- Scan.repeat1 use_prePostClause) >> USE_context_pre_post
    ||
    ((* use_invariant *)
        optional (Parse.list1 Parse.binding --| colon)
     -- Parse.binding
     -- Scan.repeat use_invariantClause
     >> USE_context_invariant)
    )
    (fn use_ctxt => fn _ =>
      case use_ctxt of USE_context_pre_post ((((name_ty, name_fun), ty_arg), ty_out), expr) =>
        OCL.OclAstCtxtPrePost (OCL.Ocl_ctxt_pre_post_ext
          ( From.from_binding name_ty
          , From.from_binding name_fun
          , From.from_list (From.from_pair From.from_binding USE_parse.from_oclty) ty_arg
          , From.from_option USE_parse.from_oclty ty_out
          , From.from_list (fn ((s_pre_post, _), expr) => ( if s_pre_post = "Pre" then OCL.OclCtxtPre else OCL.OclCtxtPost
                                                          , From.from_string expr)) expr
          , ()))
      | USE_context_invariant ((_, name), l) =>
        OCL.OclAstCtxtInv (OCL.Ocl_ctxt_inv_ext
          ( From.from_binding name
          , From.from_list (fn ((_, s), e) => (From.from_binding s, From.from_string e)) l
          , ())))
end
*}

subsection{* Outer Syntax: Class.end *}

ML{*
val () =
  outer_syntax_command @{make_string} @{command_spec "Class.end"} "Class generation"
    (Scan.optional (Parse.binding >> SOME) NONE)
    (fn _ => fn _ =>
       OCL.OclAstFlushAll (OCL.OclFlushAll))
*}

subsection{* Outer Syntax: Define_int, Instance, Define_state *}

ML{*

datatype ocl_term = OclTerm of binding
                  | OclOid of int
(*
datatype 'a ocl_l_attr = Ocl_l_attr of 'a
                    | Ocl_l_attr_cast of 'a ocl_prop * binding

and 'a ocl_prop = Ocl_prop of 'a ocl_l_attr (* l_inh *) * 'a (* l_attr *)

datatype ocl_prop_main = Ocl_prop_main of ((binding * ocl_term) list) ocl_prop
*)

val ocl_term = Parse.binding >> OclTerm
  || @{keyword "self"} |-- Parse.nat >> OclOid
val list_attr0 = Parse.binding -- (Parse.$$$ "=" |--
  (ocl_term >> (fn x => [x])
  || parse_l' ocl_term))
val list_attr00 = parse_l list_attr0
val list_attr = list_attr00 >> (fn res => (res, [] : binding list))
fun list_attr_cast00 e =
  (annot_ty list_attr00 >> (fn (res, x) => (res, [x]))
  || annot_ty list_attr_cast00 >> (fn ((res, xs), x) => (res, x :: xs))) e
val list_attr_cast = list_attr_cast00 >> (fn (res, l) => (res, rev l))

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_int"} ""
    (parse_l' Parse.number)
    (fn l_int => fn _ =>
      OCL.OclAstDefInt (OCL.OclDefI (map From.from_string l_int)))

datatype state_content = ST_l_attr of (binding * ocl_term list) list * binding (* ty *)
                       | ST_skip
                       | ST_binding of binding

val state_parse =
  (@{keyword "defines"} |-- parse_l' (list_attr_cast00 >> (fn (res, [x]) => ST_l_attr (res, x))
                                     || Parse.binding >> ST_binding))
  || @{keyword "skip"} >> K [ST_skip]

local
  fun get_oclinst l _ =
    OCL.OclInstance (map (fn ((name,typ), (l_attr, is_cast)) =>
        let val of_base = fn OclTerm s => OCL.ShallB_str (From.from_binding s)
                           | OclOid n => OCL.ShallB_self (From.from_internal_oid (From.from_nat n))
            val f = map (fn (attr, ocl) => (From.from_binding attr,
                      case ocl of [x] => OCL.Shall_base (of_base x)
                                | l => OCL.Shall_list (map of_base l)))
            val l_attr =
              fold
                (fn b => fn acc => OCL.OclAttrCast (From.from_binding b, acc, []))
                is_cast
                (OCL.OclAttrNoCast (f l_attr)) in
        OCL.Ocl_instance_single_ext
          (From.from_binding name, From.from_binding typ, l_attr, From.from_unit ()) end) l)
in
val () =
  outer_syntax_command @{make_string} @{command_spec "Instance"} ""
    (Parse.and_list1 (Parse.binding --| @{keyword "::"}
                      -- Parse.binding --| @{keyword "="}
                      -- (list_attr || list_attr_cast)))
    (OCL.OclAstInstance oo get_oclinst)

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_state"} ""
    (Parse.binding --| @{keyword "="}
     -- parse_l' state_parse)
     (fn (name, l) => fn thy =>
      OCL.OclAstDefState (OCL.OclDefSt (From.from_binding name,
        map (fn ST_l_attr (l, ty) => OCL.OclDefCoreAdd (case get_oclinst [((@{binding ""}, ty), (l, []))] thy of OCL.OclInstance [x] => x)
              | ST_skip => OCL.OclDefCoreSkip
              | ST_binding b => OCL.OclDefCoreBinding (From.from_binding b)) (List.concat l))))
end
*}

subsection{* Outer Syntax: Define_pre_post *}

ML{*
val () =
  outer_syntax_command @{make_string} @{command_spec "Define_pre_post"} ""
    (Parse.binding -- Parse.binding)
    (fn (s_pre, s_post) => fn _ =>
      OCL.OclAstDefPrePost (OCL.OclDefPP (From.from_binding s_pre, From.from_binding s_post)))

(*val _ = print_depth 100*)
*}

end
