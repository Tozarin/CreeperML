(** Copyright 2023-2024, Anton Kraev and Polina Badreeva *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

let parse_to_anf program =
  let open KREML_lib in
  let parsed_ast = Parser.parse_optimistically program in
  let _ = Inferencer.infer parsed_ast in
  let anf_conv =
    parsed_ast
    |> Clos_conv.cc_program
    |> Lambda_lifting.ll_program
    |> Anf_conv.anf_program
  in
  let anf_string =
    anf_conv |> List.map Anf_pretty_printer.string_of_abinding |> String.concat "\n"
  in
  print_endline anf_string
;;

let () = parse_to_anf (Stdio.In_channel.input_all stdin)
