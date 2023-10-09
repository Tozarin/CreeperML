(** Copyright 2023-2024, Arthur Alekseev and Starcev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

module InferUtils = struct
  open Typeast.InferType
  open Typeast.InferTypeUtils
  open Monad.Result

  (* naming and global lvl management*)
  let generic_lvl = 100500
  let marked_lvl = -1
  let gensym_counter = ref 0
  let reset_gensym () = gensym_counter := 0

  let gensym () =
    let n = !gensym_counter in
    let () = incr gensym_counter in
    if n < 26 then String.make 1 (Char.chr (Char.code 'a' + n))
    else "t" ^ string_of_int n

  let curr_lvl = ref 0
  let reset_curr_lvl () = curr_lvl := 0

  let reset_typ_vars () =
    reset_gensym ();
    reset_curr_lvl ()

  let enter_lvl () = incr curr_lvl
  let leave_lvl () = decr curr_lvl

  (* type var gen *)
  let new_var () =
    let name = gensym () in
    tv_unbound name !curr_lvl |> ref |> t_var |> with_lvls !curr_lvl !curr_lvl

  let new_arrow l r = t_arrow l r |> with_lvls !curr_lvl !curr_lvl
  let new_tuple ts = t_tuple ts |> with_lvls !curr_lvl !curr_lvl

  (* checks t for cycles *)
  let rec cyc_free t =
    match lvl_value t with
    | TVar { contents = Link t } -> cyc_free t
    | (TArrow _ | TTuple _) when t.new_lvl = marked_lvl -> error "occurse fail"
    | TArrow (l, r) ->
        let lvl = t.new_lvl in
        t.new_lvl <- marked_lvl;
        cyc_free l *> cyc_free r
        *>
        (t.new_lvl <- lvl;
         return t)
    | TTuple ts ->
        let lvl = t.new_lvl in
        t.new_lvl <- marked_lvl;
        List.fold_left
          (fun acc t -> acc *> cyc_free t)
          (List.hd ts |> cyc_free)
          (List.tl ts)
        *>
        (t.new_lvl <- lvl;
         return t)
    | _ -> return t

  (* lvlv update *)
  let lvls_to_update = ref []
  let reset_lvls_to_update () = lvls_to_update := []

  (* updates lvl of type var *)
  let update_lvl l t =
    match lvl_value t with
    | TVar ({ contents = Unbound (n, lvl) } as tvar) ->
        if lvl >= generic_lvl then error "missed invariant"
        else if l < lvl then (
          tvar := tv_unbound n lvl;
          return t)
        else return t
    | TArrow _ | TTuple _ ->
        if t.new_lvl >= generic_lvl then error "missed invariant"
        else if t.new_lvl = marked_lvl then error "occurse fail"
        else if l < t.new_lvl then
          if t.new_lvl = t.old_lvl then
            return
              (lvls_to_update := t :: !lvls_to_update;
               t.new_lvl <- l;
               t)
          else return t
        else return t
    | _ -> return t

  (* forses lvl update to type vars in backlog *)
  let force_lvls_update () =
    let rec helper acc level t =
      let t = repr t in
      match lvl_value t with
      | TVar ({ contents = Unbound (name, l) } as tvar) when l > level ->
          tvar := tv_unbound name level;
          acc
      | (TArrow _ | TTuple _) when t.new_lvl = marked_lvl ->
          error "occurse fail"
      | TArrow _ | TTuple _ ->
          if t.new_lvl > level then t.new_lvl <- level;
          update_one acc t
      | _ -> acc
    and update_one acc t =
      match lvl_value t with
      | (TArrow _ | TTuple _) when t.old_lvl <= !curr_lvl ->
          let* acc = acc in
          return (t :: acc)
      | (TArrow _ | TTuple _) when t.old_lvl = t.new_lvl -> acc
      | TArrow (l, r) ->
          let lvl = t.new_lvl in
          t.new_lvl <- marked_lvl;
          let acc = helper acc lvl l in
          let acc = helper acc lvl r in
          t.new_lvl <- lvl;
          t.old_lvl <- lvl;
          acc
      | TTuple ts ->
          let lvl = t.new_lvl in
          t.new_lvl <- marked_lvl;
          let acc = List.fold_left (fun acc t -> helper acc lvl t) acc ts in
          t.new_lvl <- lvl;
          t.old_lvl <- lvl;
          acc
      | _ -> error "never happen update_one error"
    in
    let* ls_to_update = List.fold_left update_one (return []) !lvls_to_update in
    return (lvls_to_update := ls_to_update)

  (* unifies two type vars and returned their general type *)
  let rec unify t1 t2 =
    if t1 == t2 then return t1
    else
      let t1, t2 = (repr t1, repr t2) in
      match (lvl_value t1, lvl_value t2) with
      | ( TVar ({ contents = Unbound (_, l1) } as tv1),
          TVar ({ contents = Unbound (_, l2) } as tv2) ) ->
          if tv1 == tv2 then return t1 (* think here *)
          else
            return
              (if l1 > l2 then (
                 tv1 := tv_link t2;
                 t2)
               else (
                 tv2 := tv_link t1;
                 t1))
      | TVar ({ contents = Unbound (_, l) } as tvar), _ ->
          update_lvl l t2 >>| fun t ->
          tvar := tv_link t;
          t1
      | _, TVar ({ contents = Unbound (_, l) } as tvar) ->
          update_lvl l t1 >>| fun t ->
          tvar := tv_link t;
          t2
      | TArrow (l_t1, l_t2), TArrow (r_t1, r_t2) ->
          if t1.new_lvl = marked_lvl || t2.new_lvl = marked_lvl then
            error "occurse fail"
          else
            let min_lvl = min t1.new_lvl t2.new_lvl in
            t1.new_lvl <- marked_lvl;
            t2.new_lvl <- marked_lvl;
            let* fst = unify_lev min_lvl l_t1 r_t1 in
            let* snd = unify_lev min_lvl l_t2 r_t2 in
            return
              (t1.new_lvl <- min_lvl;
               t2.new_lvl <- min_lvl;
               new_arrow fst snd) (* here think too about lvlvs*)
      | TTuple l_ts, TTuple r_ts ->
          if t1.new_lvl = marked_lvl || t2.new_lvl = marked_lvl then
            error "occurse fail"
          else
            let min_lvl = min t1.new_lvl t2.new_lvl in
            t1.new_lvl <- marked_lvl;
            t2.new_lvl <- marked_lvl;
            let* ts =
              List.fold_right2
                (fun l_t r_t acc ->
                  let* acc = acc in
                  unify_lev min_lvl l_t r_t >>| fun t -> t :: acc)
                l_ts r_ts (return [])
            in
            return
              (t1.new_lvl <- min_lvl;
               t2.new_lvl <- min_lvl;
               new_tuple ts) (* think about lvlv too *)
      | TGround l_t, TGround r_t when l_t = r_t -> return t1
      | _ ->
          Printf.sprintf "cant unify %s\n and\n %s" (show_typ t1) (show_typ t2)
          |> error

  and unify_lev l t1 t2 = repr t1 |> update_lvl l >>= fun t1 -> unify t1 t2

  (* generalise type vars *)
  let gen t =
    let rec helper t =
      let t = repr t in
      let get_lvl t =
        match lvl_value t with
        | TVar { contents = Unbound (_, l) } -> l
        | TArrow _ | TTuple _ -> t.new_lvl
        | _ -> 0
      in
      match lvl_value t with
      | TVar ({ contents = Unbound (n, l) } as tvar) when l > !curr_lvl ->
          tvar := tv_unbound n generic_lvl;
          return t
      | TArrow (l_t, r_t) when t.new_lvl > !curr_lvl ->
          let l_t, r_t = (repr l_t, repr r_t) in
          let* _ = helper l_t in
          let* _ = helper r_t in
          let l = max (get_lvl l_t) (get_lvl r_t) in
          t.new_lvl <- l;
          t.old_lvl <- l;
          return t (* new arrow? *)
      | TTuple ts when t.new_lvl > !curr_lvl ->
          let l =
            List.fold_left
              (fun acc t ->
                let t = repr t in
                let _ = helper t in
                (* maybe let* *)
                get_lvl t |> max acc)
              0 ts
          in
          t.new_lvl <- l;
          t.old_lvl <- l;
          return t (* too *)
      | _ -> return t
    in
    force_lvls_update () *> helper t

  let inst =
    let rec helper sb t =
      match lvl_value t with
      | TVar { contents = Unbound (n, l) } when l = generic_lvl -> (
          try (assoc n sb, sb)
          with Not_found ->
            let t = new_var () in
            (t, (n, t) :: sb))
      | TVar { contents = Link t } -> helper sb t
      | TArrow (l, r) when t.new_lvl = generic_lvl ->
          let l, sb = helper sb l in
          let r, sb = helper sb r in
          (new_arrow l r, sb)
      | TTuple ts when t.new_lvl = generic_lvl ->
          let ts, sb =
            List.fold_right
              (fun t (ts, sb) ->
                let t, sb = helper sb t in
                (t :: ts, sb))
              ts ([], sb)
          in
          (new_tuple ts, sb)
      | _ -> (t, sb)
    in
    fun t -> fst (helper [] t)
end

module Infer = struct
  open Parser_ast.ParserAst
  open Parser_ast.ParserAstUtils
  open InferUtils
  open Typeast.InferTypeUtils
  open Monad.Result
  open Position.Position

  (* types for inner functions *)
  type named = Named of name | NotNamed

  let named n = Named n
  let not_named = NotNamed

  let lvalue lv =
    match value lv with
    | LvAny -> (not_named, new_var ()) |> return
    | LvUnit ->
        (not_named, t_ground t_unit |> with_lvls !curr_lvl !curr_lvl) |> return
    | LvValue n -> (named n, new_var ()) |> return
    | LvTuple _ -> error "not now"

  let bind_lv_typ env lv t =
    match lv with
    | Named n -> (n, t) :: env
    | NotNamed -> env (* adds tuples to named *)

  (* tower of fantasy *)
  let tof_expr =
    let rec helper env expr =
      match value expr with
      | ELiteral l -> convert_const l |> with_lvls !curr_lvl !curr_lvl |> return
      | EValue n -> (
          try assoc n env |> return with Not_found -> error "no name")
      | ETuple es ->
          let* es =
            List.fold_right
              (fun e acc ->
                let* acc = acc in
                let* e = helper env e in
                e :: acc |> return)
              es (return [])
          in
          new_tuple es |> return
      | EFun f ->
          let* n, t_arg = lvalue f.lvalue in
          let env = bind_lv_typ env n t_arg in
          let* t_body = f.body |> value |> expr_b |> helper env in
          new_arrow t_arg t_body |> return
      | EApply (l, r) ->
          let* t_fun = helper env l in
          let* t_arg = helper env r in
          let t_res = new_var () in
          let* _ = new_arrow t_arg t_res |> unify t_fun in
          return t_res (* also aslo *)
      | EIfElse { cond = c; t_body = t; f_body = f } ->
          let* t_c = helper env c in
          let* _ =
            t_bool |> t_ground |> with_lvls !curr_lvl !curr_lvl |> unify t_c
          in
          let* t_t = helper env t in
          let* t_f = helper env f in
          unify t_t t_f (* think here *)
    in
    helper

  (* type of let expression *)
  let tof_let =
    let rec helper env { rec_f; l_v; body = b } =
      let rec_env =
        if is_rec rec_f then
          lvalue l_v >>= fun (name, t) -> bind_lv_typ env name t |> return
        else return env
      in
      enter_lvl ();
      let* inner_env =
        List.fold_left
          (fun acc l ->
            let* acc = acc in
            let* _, env = helper acc l in
            return env)
          rec_env
          (List.map value b.value.lets)
      in
      let t_e = b.value.expr |> tof_expr inner_env in
      leave_lvl ();
      t_e >>= gen >>= cyc_free >>= fun t ->
      lvalue l_v >>= fun (n, _) -> (t, bind_lv_typ env n t) |> return
    in
    helper

  (* top level inferencer *)
  let top_infer env prog =
    reset_typ_vars ();
    reset_lvls_to_update ();
    let* prog, env =
      List.fold_left
        (fun acc l ->
          let* prog, env = acc in
          let* t, env = tof_let env l in
          (t :: prog, env) |> return)
        (return ([], env))
        prog
    in
    return (List.rev prog, env)
end
