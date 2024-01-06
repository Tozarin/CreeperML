open CreeperML
open CreeperML.Parser_interface.ParserInterface
open Infer.Infer
open Indexed_ast.IndexedTypeAst
open Closure.ClosureConvert
open Anf
open Std
open Asm

let () =
  let program = from_channel stdin in
  let ( >>= ) = Result.bind in
  let apply_db_renaming p = Ok (index_of_typed Std.names p) in
  let apply_closure_convert p = Ok (cf_of_index Std.operators p) in
  let apply_anf_convert p = Ok (AnfConvert.anf_of_cf p) in
  let apply_anf_optimizations p = Ok (AnfOptimizations.optimize_moves p) in
  let apply_infer p = top_infer Std.typeenv p in
  program >>= apply_infer >>= apply_db_renaming >>= apply_closure_convert
  >>= apply_anf_convert >>= apply_anf_optimizations
  |> function
  | Ok x ->
      Asm.compile x |> AsmOptimizer.optimize
      |> Build.make_exe "../build.sh" " -l -d -b \"../../lib/bindings.o\""
  | Error x -> print_endline x
