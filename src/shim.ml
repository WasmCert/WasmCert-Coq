
let run_v comp exec monad functor monadIter project d i cfg =
  Extract.run_v_extraction comp exec monad functor monadIter project (Convert.to_nat d) i cfg

let run_step comp exec monad functor project d i cfg =
  let monadIter _ _ f =
    let rec loop i =
      Extract.bind2 Extract.__ Extract.__ (f i) (fun x ->
        let x = Obj.magic x in
        match x with
        | Extract.Inl i -> loop i
        | Extract.Inr r -> Extract.ret r) in
    loop in
  Extract.run_step_extraction comp exec monad functor monadIter project (Convert.to_nat d) i cfg

