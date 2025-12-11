(* Invoke the reference eval functions corresponding to the binary encodings (from parsing). *)

open Wasm.V128

let app_vunop_str op v =
  let vw = of_bits v in
  let wasm_f = 
    match op with
    | 77 -> V1x128.lognot
    | 96 -> I8x16.abs
    | 97 -> I8x16.neg
    | 98 -> I8x16.popcnt
    | 103 -> F32x4.ceil
    | 104 -> F32x4.floor
    | 105 -> F32x4.trunc
    | 106 -> F32x4.nearest

    | 116 -> F64x2.ceil
    | 117 -> F64x2.floor
    | 122 -> F64x2.trunc
  
    | 124 -> I16x8_convert.extadd_pairwise_s
    | 125 -> I16x8_convert.extadd_pairwise_u

    | 126 -> I32x4_convert.extadd_pairwise_s
    | 127 -> I32x4_convert.extadd_pairwise_u

    | 128 -> I16x8.abs
    | 129 -> I16x8.neg
    | 135 -> I16x8_convert.extend_low_s
    | 136 -> I16x8_convert.extend_high_s
    | 137 -> I16x8_convert.extend_low_u
    | 138 -> I16x8_convert.extend_high_u

    | 148 -> F64x2.nearest

    | 160 -> I32x4.abs
    | 161 -> I32x4.neg
    | 167 -> I32x4_convert.extend_low_s
    | 168 -> I32x4_convert.extend_high_s
    | 169 -> I32x4_convert.extend_low_u
    | 170 -> I32x4_convert.extend_high_u

    | 192 -> I64x2.abs
    | 193 -> I64x2.neg
    | 199 -> I64x2_convert.extend_low_s
    | 200 -> I64x2_convert.extend_high_s
    | 201 -> I64x2_convert.extend_low_u
    | 202 -> I64x2_convert.extend_high_u

    | 224 -> F32x4.abs
    | 225 -> F32x4.neg
    | 227 -> F32x4.sqrt

    | 236 -> F64x2.abs
    | 237 -> F64x2.neg
    | 239 -> F64x2.sqrt

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
  let (op, args) = op_args in
  let v1w = of_bits v1 in
  let v2w = of_bits v2 in
  let iop = op in
  let iargs = args in
  if iop = 13 then (* shuffle *)
    to_bits (V8x16.shuffle v1w v2w iargs)
  else
  let wasm_f = 
    match iop with
    | 14 -> V8x16.swizzle
    | 35 -> I8x16.eq
    | 36 -> I8x16.ne
    | 37 -> I8x16.lt_s
    | 38 -> I8x16.lt_u
    | 39 -> I8x16.gt_s
    | 40 -> I8x16.gt_u
    | 41 -> I8x16.le_s
    | 42 -> I8x16.le_u
    | 43 -> I8x16.ge_s
    | 44 -> I8x16.ge_u
    | 45 -> I16x8.eq
    | 46 -> I16x8.ne
    | 47 -> I16x8.lt_s
    | 48 -> I16x8.lt_u
    | 49 -> I16x8.gt_s
    | 50 -> I16x8.gt_u
    | 51 -> I16x8.le_s
    | 52 -> I16x8.le_u
    | 53 -> I16x8.ge_s
    | 54 -> I16x8.ge_u
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
    | 65 -> F32x4.eq
    | 66 -> F32x4.ne
    | 67 -> F32x4.lt
    | 68 -> F32x4.gt
    | 69 -> F32x4.le
    | 70 -> F32x4.ge
    | 71 -> F64x2.eq
    | 72 -> F64x2.ne
    | 73 -> F64x2.lt
    | 74 -> F64x2.gt
    | 75 -> F64x2.le
    | 76 -> F64x2.ge
    | 78 -> V1x128.and_
    | 79 -> V1x128.andnot
    | 80 -> V1x128.or_
    | 81 -> V1x128.xor
    | 101 -> I8x16_convert.narrow_s
    | 102 -> I8x16_convert.narrow_u
    | 110 -> I8x16.add
    | 111 -> I8x16.add_sat_s
    | 112 -> I8x16.add_sat_u
    | 113 -> I8x16.sub
    | 114 -> I8x16.sub_sat_s
    | 115 -> I8x16.sub_sat_u
    | 118 -> I8x16.min_s
    | 119 -> I8x16.min_u
    | 120 -> I8x16.max_s
    | 121 -> I8x16.max_u
    | 123 -> I8x16.avgr_u
    | 130 -> I16x8.q15mulr_sat_s
    | 133 -> I16x8_convert.narrow_s
    | 134 -> I16x8_convert.narrow_u
    | 142 -> I16x8.add
    | 143 -> I16x8.add_sat_s
    | 144 -> I16x8.add_sat_u
    | 145 -> I16x8.sub
    | 146 -> I16x8.sub_sat_s
    | 147 -> I16x8.sub_sat_u
    | 149 -> I16x8.mul
    | 150 -> I16x8.min_s
    | 151 -> I16x8.min_u
    | 152 -> I16x8.max_s
    | 153 -> I16x8.max_u
    | 155 -> I16x8.avgr_u
    | 156 -> I16x8_convert.extmul_low_s
    | 157 -> I16x8_convert.extmul_high_s
    | 158 -> I16x8_convert.extmul_low_u
    | 159 -> I16x8_convert.extmul_high_u
    | 174 -> I32x4.add
    | 177 -> I32x4.sub
    | 181 -> I32x4.mul
    | 182 -> I32x4.min_s
    | 183 -> I32x4.min_u
    | 184 -> I32x4.max_s
    | 185 -> I32x4.max_u
    | 186 -> I32x4_convert.dot_s
    | 188 -> I32x4_convert.extmul_low_s
    | 189 -> I32x4_convert.extmul_high_s
    | 190 -> I32x4_convert.extmul_low_u
    | 191 -> I32x4_convert.extmul_high_u

    | 206 -> I64x2.add
    | 209 -> I64x2.sub
    | 213 -> I64x2.mul

    | 214 -> I64x2.eq
    | 215 -> I64x2.ne
    | 216 -> I64x2.lt_s
    | 217 -> I64x2.gt_s
    | 218 -> I64x2.le_s
    | 219 -> I64x2.ge_s

    | 220 -> I64x2_convert.extmul_low_s
    | 221 -> I64x2_convert.extmul_high_s
    | 222 -> I64x2_convert.extmul_low_u
    | 223 -> I64x2_convert.extmul_high_u

    | 228 -> F32x4.add
    | 229 -> F32x4.sub
    | 230 -> F32x4.mul
    | 231 -> F32x4.div
    | 232 -> F32x4.min
    | 233 -> F32x4.max
    | 234 -> F32x4.pmin
    | 235 -> F32x4.pmax

    | 240 -> F64x2.add
    | 241 -> F64x2.sub
    | 242 -> F64x2.mul
    | 243 -> F64x2.div
    | 244 -> F64x2.min
    | 245 -> F64x2.max
    | 246 -> F64x2.pmin
    | 247 -> F64x2.pmax

    | _ -> assert false
  in
  to_bits (wasm_f v1w v2w)

let app_vternop_str op v1 v2 v3 =
  let v1w = of_bits v1 in
  let v2w = of_bits v2 in
  let v3w = of_bits v3 in
  let wasm_f = 
    match op with
    | 82 -> V1x128.bitselect
    | _ -> assert false
  in
  to_bits (wasm_f v1w v2w v3w)

let encode_bool b = 
  if b then "\x01" else "\x00"

let decode_int32 s = 
  if String.length s < 4 then invalid_arg "int32_of_le_string: need at least 4 bytes";
  let b0 = Char.code s.[0] in
  let b1 = Char.code s.[1] in
  let b2 = Char.code s.[2] in
  let b3 = Char.code s.[3] in
  let open Int32 in
  logor (of_int b0)
    (logor (shift_left (of_int b1) 8)
      (logor (shift_left (of_int b2) 16)
             (shift_left (of_int b3) 24)))

let encode_int32 x =
  let open Int32 in
  String.init 4 (function
    | 0 -> Char.chr (to_int (logand x 0xFFl))
    | 1 -> Char.chr (to_int (logand (shift_right x 8) 0xFFl))
    | 2 -> Char.chr (to_int (logand (shift_right x 16) 0xFFl))
    | 3 -> Char.chr (to_int (logand (shift_right x 24) 0xFFl))
    | _ -> assert false)

let app_vtestop_str op v1 =
  let v1w = of_bits v1 in
  let op_i = op in
  match op_i with
  | 83 -> encode_bool (I8x16.any_true v1w)

  | 99 -> encode_bool (I8x16.all_true v1w)
  | 131 -> encode_bool (I16x8.all_true v1w)
  | 163 -> encode_bool (I32x4.all_true v1w)
  | 195 -> encode_bool (I64x2.all_true v1w)

  | 100 -> encode_int32 (I8x16.bitmask v1w)
  | 132 -> encode_int32 (I16x8.bitmask v1w)
  | 164 -> encode_int32 (I32x4.bitmask v1w)
  | 196 -> encode_int32 (I64x2.bitmask v1w)

  | _ -> assert false

let app_vshiftop_str op v1 v2 =
  let v1w = of_bits v1 in
  let v2w = decode_int32 v2 in
  let wasm_f = 
    match op with
    | 107 -> I8x16.shl
    | 108 -> I8x16.shr_s
    | 109 -> I8x16.shr_u

    | 139 -> I16x8.shl
    | 140 -> I16x8.shr_s
    | 141 -> I16x8.shr_u

    | 171 -> I32x4.shl
    | 172 -> I32x4.shr_s
    | 173 -> I32x4.shr_u

    | 203 -> I64x2.shl
    | 204 -> I64x2.shr_s
    | 205 -> I64x2.shr_u

    | _ -> assert false
  in
  to_bits (wasm_f v1w v2w)