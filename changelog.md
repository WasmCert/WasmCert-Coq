#Release 2.0

This release for Wasm 2.0 implemented the following changes in the official spec release 2.0:
- Multiple-value blocks;
- Reference types;
- Table instructions;
- Multiple tables;
- Bulk memory and table instructions.

The new sign extension, non-trapping float-to-int conversion, and vector types are added but without any concrete implementation.

Some important necessary changes caused by this update are listed below:

##Values vs Instructions
Due to the introduction of reference values, values are no longer necessarily basic instructions; funcref and external ref are
expressed as administrative instructions due to their direct usage of store addresses instead of module indices. This change
has broken some assumptions that many original proofs based on. Total/partial conversion operations are now provided for 
conversion between values and their corresponding instructions.

##Value typing validity depends on store
Due to the use of store addresses, the new reference values can only be typed given a store. This necessitated the introduction
of a separate `value_typing` relation with respect to a store. In addition, value typing relation now has to be done at the
`e_typing` level (for administrative instructions) as they are no longer converted to basic instructions.


#Refactorings and other changes

##Name changes
This release included name changes to some types and constructors to better match the official spec.

##Simplification of \*id constructors
Indices are now reduced to the base `u32` type without additional constructors.

##Typing inversion lemmas and tactics
The two typing inversion tactics `invert_be_typing` and `invert_e_typing` are massively improved and can now automatically
resolve much more cases than before.
