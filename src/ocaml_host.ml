open Utils

let clock_ms () = 
  let time = Unix.gettimeofday() in
      int_of_float (time *. 1000.0)

module Ocaml_host: Extract.Parametric_host = struct

  type host_function = int
  let host_function_eq_dec a b = (a = b)

  let hfc = host_function_eq_dec

  type host_state_type = unit

  let host_apply_pure hs s ft hf vs = 
    match Obj.magic hf with
    | 0 -> 
      let ms = clock_ms () in
        ((), Some (s, Extract.Result_values [Extract.Utility.vali64_of_Z (z_of_int ms)]))
    | _ -> 
      assert false

end

let starting_wasm_host_store = 
  let hf0 = Extract.FC_func_host (Extract.Tf ([], [Extract.T_num Extract.T_i64]), Obj.magic 0) in
  let starting_wasm_store = 
    {Extract.s_funcs = [hf0]; 
     Extract.s_tables = []; 
     Extract.s_mems = []; 
     Extract.s_globals = []; 
     Extract.s_elems = []; 
     Extract.s_datas = []
    } 
  in
  let env_module_exps = StringMap.add "clock_ms"  (Extract.EV_func (z_of_int 0)) Utils.StringMap.empty in 
  let module_extern_store = StringMap.add "env" env_module_exps Utils.StringMap.empty in
  let module_name_store = StringMap.add "env" "env" Utils.StringMap.empty in
  let starting_host_store = (module_extern_store, module_name_store) in
  (starting_wasm_store, starting_host_store)