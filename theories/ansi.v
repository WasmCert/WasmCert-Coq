
Require Import Coq.Strings.String.
Open Scope string_scope.

Definition ansi_escape_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x1b.

Definition ansi_escape : string := String ansi_escape_char EmptyString.

Definition ansi_reset : string := ansi_escape ++ "[0m".
Definition ansi_bold : string := ansi_escape ++ "[1m".
Definition ansi_red : string := ansi_escape ++ "[31m".
Definition ansi_green : string := ansi_escape ++ "[32m".