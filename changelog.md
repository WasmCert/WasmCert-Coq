# Release 2.0

This release for Wasm 2.0 implemented the following changes in the official spec release 2.0:
- Multiple-value blocks;
- Reference types;
- Table instructions;
- Multiple tables;
- Bulk memory and table instructions.

The new sign extension, non-trapping float-to-int conversion, and vector types are added but without any concrete implementation.

## Updated Components:
[x] Base opsem/typing definitions;
[x] Type preservation theorem (except store extension theorems for now);
[x] Interpreter and progress theorem;
[x] Instantiation;
[ ] Instantiation soundness theorems;
[x] Type checker;
[ ] Type checker correctness theorem;
[x] Binary printer/parser;
[x] Code pretty printer.

# Major Structural Changes

## Values vs Instructions
Due to the introduction of reference values, values are no longer necessarily basic instructions; funcref and external ref are
expressed as administrative instructions due to their direct usage of store addresses instead of module indices. This change
has broken some assumptions that many original proofs based on. Total/partial conversion operations are now provided for 
conversion between values and their corresponding instructions.

## Value typing validity depends on store
Due to the use of store addresses, the new reference values can only be typed given a store. This necessitated the introduction
of a separate `value_typing` relation with respect to a store. In addition, value typing relation now has to be done at the
`e_typing` level (for administrative instructions) as they are no longer converted to basic instructions.

## Threads
Threads are now properly spelt out as a separate type that constitutes the configuration tuple. The old thread-related definitions (e.g. `s_typing`) are renamed to the names used in the standard (e.g. `thread_typing`).


# Refactorings and Feature Improvements

## Host Formulation
The parametric host language is now defined using typeclasses. 
The main major benefit is the automatic filling of implicit host parameter, instead of needing to redefine all operations involving anything downstream from function instances and stores. The proof context is also greatly simplified since all these redefinitions no longer exist to occupy a major chunk of the buffer window.


## Numerics
- Refactored the old collection of conversion operations *cvtop* to be split up by their individual constructors.

## Name Changes
- Changed the name of some types, instructions, and constructors to better match the official spec.
- Instance indices are now reduced to the base `u32` type without additional constructors.

## Binary Parser/Printer
- 

## Pretty Printer
- Implemented pretty printing for conversion operations.

## Typing
- Massively improved the scope and automation of the typing inversion lemmas.
- Provided a new tactic `resolve_e_typing` that automatically tries to resolve `e_typing` goals, dealing mostly with the operands.

## Miscellaneous
- Introduced many additional excerpts in comments from the official spec for various definitions.

# Bug Fixes
- Fixed a bug where the binary printer incorrectly prints all types of reinterpret conversions to 0xBC.
- Fixed a bug where the binary printer sometimes prints indices via a conversion to nat first.
