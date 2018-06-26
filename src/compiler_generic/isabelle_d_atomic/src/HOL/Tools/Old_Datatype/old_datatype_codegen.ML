(*  Title:      HOL/Tools/Old_Datatype/old_datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature OLD_DATATYPE_CODEGEN =
sig
end;

structure Old_Datatype_Codegen : OLD_DATATYPE_CODEGEN =
struct

fun add_code_for_datatype config fcT_name =
  if #skip_level config >= 2 then I else fn thy =>
  let
    val ctxt = Proof_Context.init_global thy
  in
    case Ctr_Sugar.ctr_sugar_of ctxt fcT_name of
      SOME {ctrs, injects, distincts, case_thms, ...} =>
        let val Type (_, As) = body_type (fastype_of (hd ctrs))
        in Ctr_Sugar_Code.add_ctr_code fcT_name As (map dest_Const ctrs) injects distincts case_thms thy end
    | _ => thy
  end;

val _ = Theory.setup (Old_Datatype_Data.interpretation (fold o add_code_for_datatype));

end;
