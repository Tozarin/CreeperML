(** Copyright 2023-2024, Danila Pechenev, Ilya Dudnikov *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast

type error_message = string
type input = string

val parse : input -> (declaration list, error_message) result
