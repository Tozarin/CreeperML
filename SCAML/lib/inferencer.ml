(* http://dev.stephendiehl.com/fun/006_hindley_milner.html *)

open Base
open Ty
module Format = Caml.Format (* silencing a warning *)

let use_logging = false

let log fmt =
  if use_logging
  then Format.kasprintf (fun s -> Format.printf "%s\n%!" s) fmt
  else Format.ifprintf Format.std_formatter fmt
;;

type error =
  [ `Occurs_check
  | `No_variable of string
  | `Unification_failed of ty * ty
  ]

let pp_error ppf : error -> _ = function
  | `Occurs_check -> Format.fprintf ppf "Occurs check failed"
  | `No_variable s -> Format.fprintf ppf "Undefined variable '%s'" s
  | `Unification_failed (l, r) ->
    Format.fprintf ppf "unification failed on %a and %a" pp_typ l pp_typ r
;;

module R : sig
  type 'a t

  val bind : 'a t -> f:('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val fail : error -> 'a t

  include Monad.Infix with type 'a t := 'a t

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  module RMap : sig
    val fold_left
      :  (int, 'a, Base.Int.comparator_witness) Base.Map.t
      -> init:'b t
      -> f:('b -> int * 'a -> 'b t)
      -> 'b t
  end

  (** Creation of a fresh name from internal state *)
  val fresh : int t

  (** Running a transformer: getting the inner result value *)
  val run : 'a t -> ('a, error) Result.t
end = struct
  (* A compositon: State monad after Result monad *)
  type 'a t = int -> int * ('a, error) Result.t

  let ( >>= ) : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
    fun m f st ->
    let last, r = m st in
    match r with
    | Result.Error x -> last, Error x
    | Ok a -> f a last
  ;;

  let fail e st = st, Result.fail e
  let return x last = last, Result.return x
  let bind x ~f = x >>= f

  let ( >>| ) : 'a 'b. 'a t -> ('a -> 'b) -> 'b t =
    fun x f st ->
    match x st with
    | st, Ok x -> st, Ok (f x)
    | st, Result.Error e -> st, Result.Error e
  ;;

  module Syntax = struct
    let ( let* ) x f = bind x ~f
  end

  module RMap = struct
    let fold_left map ~init ~f =
      Map.fold map ~init ~f:(fun ~key ~data acc ->
        let open Syntax in
        let* acc = acc in
        f acc (key, data))
    ;;
  end

  let fresh : int t = fun last -> last + 1, Result.Ok last
  let run m = snd (m 0)
end

type fresh = int

module Type = struct
  type t = ty

  (* проверяет встерчается ли искомый TVar в выражении *)
  let rec occurs_in v = function
    | TVar b -> b = v
    | TArrow (l, r) -> occurs_in v l || occurs_in v r
    | TInt | TBool -> false
  ;;

  (* Возвращает сет всех типовых переменых, которые встречаются в выражении*)
  let free_vars =
    let rec helper acc = function
      | TVar b -> VarSet.add b acc
      | TArrow (l, r) -> helper (helper acc l) r
      | TInt | TBool -> acc
    in
    helper VarSet.empty
  ;;
end

module Subst : sig
  type t

  val pp : Caml.Format.formatter -> t -> unit
  val empty : t
  val singleton : fresh -> ty -> t R.t

  (** Getting value from substitution. May raise [Not_found] *)
  val find_exn : fresh -> t -> ty

  val find : fresh -> t -> ty option
  val apply : t -> ty -> ty
  val unify : ty -> ty -> t R.t

  (** Compositon of substitutions *)
  val compose : t -> t -> t R.t

  val compose_all : t list -> t R.t
  val remove : t -> fresh -> t
end = struct

  open R
  open R.Syntax
  
  type t = (fresh, ty, Int.comparator_witness) Map.t

  let pp ppf subst =
    let list = Map.to_alist subst in
    let open Format in
    fprintf
      ppf
      "[ %a ]"
      (pp_print_list
         ~pp_sep:(fun ppf () -> fprintf ppf ", ")
         (fun ppf (k, v) -> fprintf ppf "%d -> %a" k pp_typ v))
      list
  ;;

  let empty = Map.empty (module Int)
  let mapping k v = if Type.occurs_in k v then fail `Occurs_check else return (k, v)

  let singleton k v =
    let* k, v = mapping k v in
    return  (Map.singleton (module Int) k v)
  ;;

  let find_exn k xs = Base.Map.find_exn xs k
  let find k xs = Base.Map.find xs k
  let remove xs k = Base.Map.remove xs k

  (* Подставляет типы в выражение согласно контексту из списка и  возвращает результат замены*)
  let apply s =
    let rec helper = function
      | TVar b as ty ->
        (match find b s with
         | None -> ty
         | Some x -> x)
      | TArrow (l, r) -> TArrow (helper l, helper r)
      | other -> other
    in
    helper
  ;;

  (* Пытается унифицировать(Также проверить совместимость двх выражений по типам) типы двух выражений и возвращает либо ошибку,
     либо результат(ассоциативный список с "номером" типа и типом) либо ошибку *)
  let rec unify l r =
    match l, r with
    | TInt, TInt | TBool, TBool -> return empty
    | TVar a, TVar b when Int.equal a b -> return empty
    | TVar b, t | t, TVar b -> singleton b t
    | TArrow (l1, r1), TArrow (l2, r2) ->
      let* subs1 = unify l1 l2 in
      let* subs2 = unify (apply subs1 r1) (apply subs1 r2) in
      compose subs1 subs2
    | _ -> fail (`Unification_failed (l, r))

  (* Следующие функции помогают объеденить два ассоцитавных списка*)

  (* расширяет контекст новой переменной типа, либо добавляя ее в список и применяя к ней все из контекста, либо унифицируя ее тип*)
  and extend s (k, v) =
    match find k s with
    | None ->
      let v = apply s v in
      let* s2 = singleton k v in
      RMap.fold_left s ~init:(return s2) ~f:(fun acc (k, v) ->
        let v = apply s2 v in
        let* k, v = mapping k v in
        return (Map.add_exn acc ~key:k ~data:v))
    | Some v2 ->
      let* s2 = unify v v2 in
      compose s s2

  and compose s1 s2 = RMap.fold_left s2 ~init:(return s1) ~f:extend

  let compose_all ss = List.fold_left ss ~init:(return empty) ~f: (fun acc ss -> let* acc = acc in compose acc ss)
end

module VarSet = struct
  include VarSet

  let fold_left_m f acc set =
    fold
      (fun x acc ->
        let open R.Syntax in
        let* acc = acc in
        f acc x)
      acc
      set
  ;;
end

module Scheme = struct
  type t = scheme

  (* Проверяет встречается ли в схеме (варсете и типовом выражении) данная типовая переменная *)
  let occurs_in v = function
    | S (xs, t) -> (not (VarSet.mem v xs)) && Type.occurs_in v t
  ;;

  (* Возвращает все типовые переменные, которые есть в выражении, но нет в сете*)
  let free_vars = function
    | S (bs, t) -> VarSet.diff (Type.free_vars t) bs
  ;;

  (* Возвращает новую схему, удаляя из ассоциативного списка все что есть в varset и применяя к типовому выражению полученный список
     (насколько я понимаю это сделано для того, чтобы задавать локальный контекст)*)
  let apply sub (S (names, ty)) =
    let s2 = VarSet.fold (fun k s -> Subst.remove s k) names sub in
    S (names, Subst.apply s2 ty)
  ;;

  let pp = pp_scheme
end

module TypeEnv = struct
  type t = (string * scheme) list

  let extend e h = h :: e
  let empty = []

  (* Просто возвращает все переменные, которые есть во всех выражениях, но нет в сетах*)
  let free_vars : t -> VarSet.t =
    List.fold_left ~init:VarSet.empty ~f:(fun acc (_, s) ->
      VarSet.union acc (Scheme.free_vars s))
  ;;

  let apply s env = List.Assoc.map env ~f:(Scheme.apply s)

  let pp ppf xs =
    Caml.Format.fprintf ppf "{| ";
    List.iter xs ~f:(fun (n, s) ->
      Caml.Format.fprintf ppf "%s -> %a; " n pp_scheme s);
    Caml.Format.fprintf ppf "|}%!"
  ;;

  let find_exn name xs = List.Assoc.find_exn ~equal:String.equal xs name
end

open R
open R.Syntax

let unify = Subst.unify
let fresh_var = fresh >>| fun n -> TVar n

(* Создает новые fresh_var и заменяет ими старые типовые переменные в выражении
(Насколько я понял это нужно чтобы уточнять тип функции в каждом конкретном случае)*)
let instantiate : scheme -> ty R.t =
  fun (S (bs, t)) ->
  VarSet.fold_left_m
    (fun typ name ->
      let* f1 = fresh_var in
      let* s = Subst.singleton name f1 in
      return (Subst.apply s typ))
    bs
    (return t)
;;

let generalize : TypeEnv.t -> Type.t -> Scheme.t =
  fun env ty ->
  let free = VarSet.diff (Type.free_vars ty) (TypeEnv.free_vars env) in
  S (free, ty)
;;

(* достает из окружения схему функции *)
let lookup_env e xs =
  match List.Assoc.find_exn xs ~equal:String.equal e with
  | (exception Caml.Not_found) | (exception Not_found_s _) -> fail (`No_variable e)
  | scheme ->
    let* ans = instantiate scheme in
    return (Subst.empty, ans)
;;

let pp_env subst ppf env =
  let env : TypeEnv.t =
    List.map ~f:(fun (k, S (args, v)) -> k, S (args, Subst.apply subst v)) env
  in
  TypeEnv.pp ppf env
;;

let infer =
  let rec (helper : TypeEnv.t -> Parsetree.expr -> (Subst.t * ty) R.t) =
    fun env -> function
    | Parsetree.EVar "*" | Parsetree.EVar "-" | Parsetree.EVar "+" ->
      return (Subst.empty, arrow int_typ (arrow int_typ int_typ))
    | Parsetree.EVar "=" -> return (Subst.empty, arrow int_typ (arrow int_typ bool_typ))
    | Parsetree.EVar x -> lookup_env x env
    | ELam (PVar x, e1) ->
      let* tv = fresh_var in
      let env2 = TypeEnv.extend env (x, S (VarSet.empty, tv)) in
      let* s, ty = helper env2 e1 in
      let trez = TArrow (Subst.apply s tv, ty) in
      return (s, trez)
    | EApp (e1, e2) ->
      let* s1, t1 = helper env e1 in
      let* s2, t2 = helper (TypeEnv.apply s1 env) e2 in
      let* tv = fresh_var in
      let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv)) in
      let trez = Subst.apply s3 tv in
      let* final_subst = Subst.compose_all [ s3; s2; s1 ] in
      return (final_subst, trez)
    | EConst _n -> return (Subst.empty, Prim "int")
    | Parsetree.EIf (c, th, el) ->
      let* s1, t1 = helper env c in
      let* s2, t2 = helper env th in
      let* s3, t3 = helper env el in
      let* s4 = unify t1 (Prim "bool") in
      let* s5 = unify t2 t3 in
      let* final_subst = Subst.compose_all [ s5; s4; s3; s2; s1 ] in
      R.return (final_subst, Subst.apply s5 t2)
    | Parsetree.ELet (NonRecursive, PVar x, e1, e2) ->
      let* s1, t1 = helper env e1 in
      let env2 = TypeEnv.apply s1 env in
      let t2 = generalize env2 t1 in
      let* s2, t3 = helper (TypeEnv.extend env2 (x, t2)) e2 in
      let* final_subst = Subst.compose s1 s2 in
      return (Subst.(final_subst), t3)
    | Parsetree.ELet (Recursive, PVar x, e1, e2) ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (x, S (VarSet.empty, tv)) in
      let* s1, t1 = helper env e1 in
      let* s2 = unify (Subst.apply s1 tv) t1 in
      let* s = Subst.compose s2 s1 in
      let env = TypeEnv.apply s env in
      let t2 = generalize env (Subst.apply s tv) in
      let* s2, t2 = helper TypeEnv.(extend (apply s env) (x, t2)) e2 in
      let* final_subst = Subst.compose s s2 in
      return (final_subst, t2)
  in
  helper
;;

let w e = Result.map (run (infer TypeEnv.empty e)) ~f:snd

(** {3} Tests *)

let run_subst subst =
  match R.run subst with
  | Result.Error _ -> Format.printf "Error%!"
  | Ok subst -> Format.printf "%a%!" Subst.pp subst
;;

let%expect_test _ =
  let _ = unify (v 1 @-> v 1) (int_typ @-> v 2) |> run_subst in
  [%expect {| [ 1 -> int, 2 -> int ] |}]
;;

let%expect_test _ =
  let _ = unify (v 1 @-> v 1) ((v 2 @-> int_typ) @-> int_typ @-> int_typ) |> run_subst in
  [%expect {| [ 1 -> (int -> int), 2 -> int ] |}]
;;

let%expect_test _ =
  let _ = unify (v 1 @-> v 2) (v 2 @-> v 3) |> run_subst in
  [%expect {| [ 1 -> '_3, 2 -> '_3 ] |}]
;;

let%expect_test "Getting free variables from type scheme" =
  let _ =
    Format.printf
      "%a%!"
      VarSet.pp
      (Scheme.free_vars (S (VarSet.singleton 1, v 1 @-> v 2)))
  in
  [%expect {| [ 2; ] |}]
;;
