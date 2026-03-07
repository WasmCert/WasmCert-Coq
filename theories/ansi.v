
(** ANSI escape sequences -- work in progress *)
Require Import Coq.Strings.String.
Open Scope string_scope.

Definition ansi_escape_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x1b.

Definition ansi_escape : string := String ansi_escape_char EmptyString.

Inductive ansi_fg : Type :=
| FG_reset
| FG_green
| FG_red
| FG_yellow
| FG_blue
| FG_magenta
| FG_cyan
| FG_bold.

Definition code_of_fg (fg : ansi_fg) : string :=
  match fg with
  | FG_reset => "0"
  | FG_bold => "1"
  | FG_red => "31"
  | FG_green => "32"
  | FG_yellow => "33"
  | FG_blue => "34"
  | FG_magenta => "35"
  | FG_cyan => "36"
  end.

Definition show_fg (fg : ansi_fg) : string :=
  ansi_escape ++ "[" ++ code_of_fg fg ++ "m".

Definition with_fg (fg : ansi_fg) (s : string) : string :=
  show_fg fg ++ s ++ show_fg FG_reset.