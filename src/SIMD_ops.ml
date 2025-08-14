open Wasm.V128

let app_vunop_str op v =
  let vw = of_bits v in
  let wasm_f = 
    match Utils.int_of_z op with
    | 160 -> I32x4.abs
    | 161 -> I32x4.neg
    | 248 -> I32x4_convert.trunc_sat_f32x4_s
    | 249 -> I32x4_convert.trunc_sat_f32x4_u
    | 250 -> F32x4_convert.convert_i32x4_s
    | 251 -> F32x4_convert.convert_i32x4_u
    | 252 -> I32x4_convert.trunc_sat_f64x2_s_zero
    | 253 -> I32x4_convert.trunc_sat_f64x2_u_zero
    | 254 -> F64x2_convert.convert_i32x4_s (* low missing from the op name *)
    | 255 -> F64x2_convert.convert_i32x4_u (* low missing from the op name *)
    | 94 -> F32x4_convert.demote_f64x2_zero
    | 95 -> F64x2_convert.promote_low_f32x4
    | _ -> assert false
  in
  to_bits (wasm_f vw)

let app_vbinop_str op_args v1 v2 = 
  let (op, _args) = op_args in
  let v1w = of_bits v1 in
  let v2w = of_bits v2 in
  let wasm_f = 
    match Utils.int_of_z op with
    | 55 -> I32x4.eq
    | 56 -> I32x4.ne
    | 57 -> I32x4.lt_s
    | 58 -> I32x4.lt_u
    | 59 -> I32x4.gt_s
    | 60 -> I32x4.gt_u
    | 61 -> I32x4.le_s
    | 62 -> I32x4.le_u
    | 63 -> I32x4.ge_s
    | 64 -> I32x4.ge_u
    | 174 -> I32x4.add
    | 177 -> I32x4.sub
    | 181 -> I32x4.mul
    | 182 -> I32x4.min_s
    | 183 -> I32x4.min_u
    | 184 -> I32x4.max_s
    | 185 -> I32x4.max_u
    | 188 -> I32x4_convert.extmul_low_s
    | 189 -> I32x4_convert.extmul_high_s
    | 190 -> I32x4_convert.extmul_low_u
    | 191 -> I32x4_convert.extmul_high_u
    | 206 -> I64x2.add
    | _ -> assert false
  in
  to_bits (wasm_f v1w v2w)

let app_vternop_str op v1 v2 v3 =
  let v1w = of_bits v1 in
  let v2w = of_bits v2 in
  let v3w = of_bits v3 in
  let wasm_f = 
    match Utils.int_of_z op with
    | 82 -> V1x128.bitselect
    | _ -> assert false
  in
  to_bits (wasm_f v1w v2w v3w)