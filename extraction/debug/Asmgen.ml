(* Replace transl_op by this wrapper to print the op *)

let thereal_transl_op op args res0 k =
  match op with
  | Ointconst n ->
    (match args with
     | [] ->
       (match ireg_of res0 with
        | OK x -> OK (loadimm32 x n k)
        | Error msg0 -> Error msg0)
     | _ :: _ ->
       Error
         (msg
           ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[]))))))))))))))))))
  | Olongconst n ->
    (match args with
     | [] ->
       (match ireg_of res0 with
        | OK x -> OK (loadimm64 x n k)
        | Error msg0 -> Error msg0)
     | _ :: _ ->
       Error
         (msg
           ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[]))))))))))))))))))
  | Oaddl ->
    (match args with
     | [] ->
       Error
         (msg
           ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[])))))))))))))))))
     | a1 :: l ->
       (match l with
        | [] ->
          Error
            (msg
              ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[])))))))))))))))))
        | a2 :: l0 ->
          (match l0 with
           | [] ->
             (match ireg_of res0 with
              | OK x ->
                (match ireg_of a1 with
                 | OK x0 ->
                   (match ireg_of a2 with
                    | OK x1 -> OK ((Paddl (x, x0, x1)) :: k)
                    | Error msg0 -> Error msg0)
                 | Error msg0 -> Error msg0)
              | Error msg0 -> Error msg0)
           | _ :: _ ->
             Error
               (msg
                 ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[]))))))))))))))))))))
  | Oaddlimm n ->
    (match args with
     | [] ->
       Error
         (msg
           ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[])))))))))))))))))
     | a1 :: l ->
       (match l with
        | [] ->
          (match ireg_of res0 with
           | OK x ->
             (match ireg_of a1 with
              | OK x0 -> OK (addimm64 x x0 n k)
              | Error msg0 -> Error msg0)
           | Error msg0 -> Error msg0)
        | _ :: _ ->
          Error
            (msg
              ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[])))))))))))))))))))
  | _ ->
    Error
      (msg
        ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('o'::('p'::[])))))))))))))))))

let transl_op op args res0 k =
  match op with
  | Omove -> (Printf.eprintf "Omove\n"; thereal_transl_op op args res0 k)
  | Ointconst _ -> (Printf.eprintf "Ointconst _\n"; thereal_transl_op op args res0 k)
  | Olongconst _ -> (Printf.eprintf "Olongconst _\n"; thereal_transl_op op args res0 k)
  | Ofloatconst _ -> (Printf.eprintf "Ofloatconst _\n"; thereal_transl_op op args res0 k)
  | Osingleconst _ -> (Printf.eprintf "Osingleconst _\n"; thereal_transl_op op args res0 k)
  | Oaddrsymbol _ -> (Printf.eprintf "Oaddrsymbol _ _\n"; thereal_transl_op op args res0 k)
  | Oaddrstack _ -> (Printf.eprintf "Oaddrstack _\n"; thereal_transl_op op args res0 k)
  | Ocast8signed -> (Printf.eprintf "Ocast8signed\n"; thereal_transl_op op args res0 k)
  | Ocast16signed -> (Printf.eprintf "Ocast16signed\n"; thereal_transl_op op args res0 k)
  | Oadd -> (Printf.eprintf "Oadd\n"; thereal_transl_op op args res0 k)
  | Oaddimm _ -> (Printf.eprintf "Oaddimm _\n"; thereal_transl_op op args res0 k)
  | Oneg -> (Printf.eprintf "Oneg\n"; thereal_transl_op op args res0 k)
  | Osub -> (Printf.eprintf "Osub\n"; thereal_transl_op op args res0 k)
  | Omul -> (Printf.eprintf "Omul\n"; thereal_transl_op op args res0 k)
  | Omulhs -> (Printf.eprintf "Omulhs\n"; thereal_transl_op op args res0 k)
  | Omulhu -> (Printf.eprintf "Omulhu\n"; thereal_transl_op op args res0 k)
  | Odiv -> (Printf.eprintf "Odiv\n"; thereal_transl_op op args res0 k)
  | Odivu -> (Printf.eprintf "Odivu\n"; thereal_transl_op op args res0 k)
  | Omod -> (Printf.eprintf "Omod\n"; thereal_transl_op op args res0 k)
  | Omodu -> (Printf.eprintf "Omodu\n"; thereal_transl_op op args res0 k)
  | Oand -> (Printf.eprintf "Oand\n"; thereal_transl_op op args res0 k)
  | Oandimm _ -> (Printf.eprintf "Oandimm _\n"; thereal_transl_op op args res0 k)
  | Oor -> (Printf.eprintf "Oor\n"; thereal_transl_op op args res0 k)
  | Oorimm _ -> (Printf.eprintf "Oorimm _\n"; thereal_transl_op op args res0 k)
  | Oxor -> (Printf.eprintf "Oxor\n"; thereal_transl_op op args res0 k)
  | Oxorimm _ -> (Printf.eprintf "Oxorimm _\n"; thereal_transl_op op args res0 k)
  | Oshl -> (Printf.eprintf "Oshl\n"; thereal_transl_op op args res0 k)
  | Oshlimm _ -> (Printf.eprintf "Oshlimm _\n"; thereal_transl_op op args res0 k)
  | Oshr -> (Printf.eprintf "Oshr\n"; thereal_transl_op op args res0 k)
  | Oshrimm _ -> (Printf.eprintf "Oshrimm _\n"; thereal_transl_op op args res0 k)
  | Oshruimm _ -> (Printf.eprintf "Oshruimm _\n"; thereal_transl_op op args res0 k)
  | Oshrximm _ -> (Printf.eprintf "Oshrximm _\n"; thereal_transl_op op args res0 k)
  | Olowlong -> (Printf.eprintf "Olowlong\n"; thereal_transl_op op args res0 k)
  | Ocast32signed -> (Printf.eprintf "Ocast32signed\n"; thereal_transl_op op args res0 k)
  | Ocast32unsigned -> (Printf.eprintf "Ocast32unsigned\n"; thereal_transl_op op args res0 k)
  | Oaddl -> (Printf.eprintf "Oaddl\n"; thereal_transl_op op args res0 k)
  | Oaddlimm _ -> (Printf.eprintf "Oaddlimm _\n"; thereal_transl_op op args res0 k)
  | Onegl -> (Printf.eprintf "Onegl\n"; thereal_transl_op op args res0 k)
  | Osubl -> (Printf.eprintf "Osubl\n"; thereal_transl_op op args res0 k)
  | Omull -> (Printf.eprintf "Omull\n"; thereal_transl_op op args res0 k)
  | Omullhs -> (Printf.eprintf "Omullhs\n"; thereal_transl_op op args res0 k)
  | Omullhu -> (Printf.eprintf "Omullhu\n"; thereal_transl_op op args res0 k)
  | Odivl -> (Printf.eprintf "Odivl\n"; thereal_transl_op op args res0 k)
  | Odivlu -> (Printf.eprintf "Odivlu\n"; thereal_transl_op op args res0 k)
  | Omodl -> (Printf.eprintf "Omodl\n"; thereal_transl_op op args res0 k)
  | Omodlu -> (Printf.eprintf "Omodlu\n"; thereal_transl_op op args res0 k)
  | Oandl -> (Printf.eprintf "Oandl\n"; thereal_transl_op op args res0 k)
  | Oandlimm _ -> (Printf.eprintf "Oandlimm _\n"; thereal_transl_op op args res0 k)
  | Oorl -> (Printf.eprintf "Oorl\n"; thereal_transl_op op args res0 k)
  | Oorlimm _ -> (Printf.eprintf "Oorlimm _\n"; thereal_transl_op op args res0 k)
  | Oxorl -> (Printf.eprintf "Oxorl\n"; thereal_transl_op op args res0 k)
  | Oxorlimm _ -> (Printf.eprintf "Oxorlimm _\n"; thereal_transl_op op args res0 k)
  | Oshll -> (Printf.eprintf "Oshll\n"; thereal_transl_op op args res0 k)
  | Oshllimm _ -> (Printf.eprintf "Oshllimm _\n"; thereal_transl_op op args res0 k)
  | Oshrlu -> (Printf.eprintf "Oshrlu\n"; thereal_transl_op op args res0 k)
  | Oshrluimm _ -> (Printf.eprintf "Oshrluimm\n"; thereal_transl_op op args res0 k)
  | Oshrxlimm _ -> (Printf.eprintf "Oshrxlimm\n"; thereal_transl_op op args res0 k)
  | Onegf -> (Printf.eprintf "Onegf\n"; thereal_transl_op op args res0 k)
  | Oabsf -> (Printf.eprintf "Oabsf\n"; thereal_transl_op op args res0 k)
  | Oaddf -> (Printf.eprintf "Oaddf\n"; thereal_transl_op op args res0 k)
  | Osubf -> (Printf.eprintf "Osubf\n"; thereal_transl_op op args res0 k)
  | Omulf -> (Printf.eprintf "Omulf\n"; thereal_transl_op op args res0 k)
  | Odivf -> (Printf.eprintf "Odivf\n"; thereal_transl_op op args res0 k)
  | Onegfs -> (Printf.eprintf "Onegfs\n"; thereal_transl_op op args res0 k)
  | Oabsfs -> (Printf.eprintf "Oabsfs\n"; thereal_transl_op op args res0 k)
  | Oaddfs -> (Printf.eprintf "Oaddfs\n"; thereal_transl_op op args res0 k)
  | Osubfs -> (Printf.eprintf "Osubfs\n"; thereal_transl_op op args res0 k)
  | Omulfs -> (Printf.eprintf "Omulfs\n"; thereal_transl_op op args res0 k)
  | Odivfs -> (Printf.eprintf "Odivfs\n"; thereal_transl_op op args res0 k)
  | Osingleoffloat -> (Printf.eprintf "Osingleoffloat\n"; thereal_transl_op op args res0 k)
  | Ofloatofsingle -> (Printf.eprintf "Ofloatofsingle\n"; thereal_transl_op op args res0 k)
  | Ointoffloat -> (Printf.eprintf "Ointoffloat\n"; thereal_transl_op op args res0 k)
  | Ointuoffloat -> (Printf.eprintf "Ointuoffloat\n"; thereal_transl_op op args res0 k)
  | Ofloatofint -> (Printf.eprintf "Ofloatofint\n"; thereal_transl_op op args res0 k)
  | Ofloatofintu -> (Printf.eprintf "Ofloatofintu\n"; thereal_transl_op op args res0 k)
  | Ointofsingle -> (Printf.eprintf "Ointofsingle\n"; thereal_transl_op op args res0 k)
  | Ointuofsingle -> (Printf.eprintf "Ointuofsingle\n"; thereal_transl_op op args res0 k)
  | Osingleofint -> (Printf.eprintf "Osingleofint\n"; thereal_transl_op op args res0 k)
  | Osingleofintu -> (Printf.eprintf "Osingleofintu\n"; thereal_transl_op op args res0 k)
  | Olongoffloat -> (Printf.eprintf "Olongoffloat\n"; thereal_transl_op op args res0 k)
  | Olonguoffloat -> (Printf.eprintf "Olonguoffloat\n"; thereal_transl_op op args res0 k)
  | Ofloatoflong -> (Printf.eprintf "Ofloatoflong\n"; thereal_transl_op op args res0 k)
  | Ofloatoflongu -> (Printf.eprintf "Ofloatoflongu\n"; thereal_transl_op op args res0 k)
  | Olongofsingle -> (Printf.eprintf "Olongofsingle\n"; thereal_transl_op op args res0 k)
  | Olonguofsingle -> (Printf.eprintf "Olonguofsingle\n"; thereal_transl_op op args res0 k)
  | Osingleoflong -> (Printf.eprintf "Osingleoflong\n"; thereal_transl_op op args res0 k)
  | Osingleoflongu -> (Printf.eprintf "Osingleoflongu\n"; thereal_transl_op op args res0 k)
  | Ocmp _ -> (Printf.eprintf "Ocmp _\n"; thereal_transl_op op args res0 k)
  | _ -> (Printf.eprintf "_\n"; thereal_transl_op op args res0 k)

let thereal_transl_instr f i _ k =
  match i with
  | Mop (op, args, res0) -> transl_op op args res0 k
  | Mbuiltin (ef, args, res0) ->
    OK ((Pbuiltin (ef, (map (map_builtin_arg preg_of) args),
      (map_builtin_res preg_of res0))) :: k)
  | Mlabel lbl -> OK ((Plabel lbl) :: k)
  | Mreturn -> OK (make_epilogue f (Pret :: k))
  | _ ->
    Error
      (msg
        ('A'::('s'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('i'::('n'::('s'::('t'::('r'::[]))))))))))))))))))))

let transl_instr f i _ k =
  match i with
  | Mgetstack _ -> (Printf.eprintf "Mgetstack\n"; thereal_transl_instr f i x k)
  | Msetstack _ -> (Printf.eprintf "Msetstack\n"; thereal_transl_instr f i x k)
  | Mgetparam _ -> (Printf.eprintf "Mgetparam\n"; thereal_transl_instr f i x k)
  | Mop _ -> (Printf.eprintf "Mop\n"; thereal_transl_instr f i x k)
  | Mload _ -> (Printf.eprintf "Mload\n"; thereal_transl_instr f i x k)
  | Mstore _ -> (Printf.eprintf "Mstore\n"; thereal_transl_instr f i x k)
  | Mcall _ -> (Printf.eprintf "Mcall\n"; thereal_transl_instr f i x k)
  | Mtailcall _ -> (Printf.eprintf "Mtailcall\n"; thereal_transl_instr f i x k)
  | Mbuiltin _ -> (Printf.eprintf "Mbuiltin\n"; thereal_transl_instr f i x k)
  | Mlabel _ -> (Printf.eprintf "Mlabel\n"; thereal_transl_instr f i x k)
  | Mgoto _ -> (Printf.eprintf "Mgoto\n"; thereal_transl_instr f i x k)
  | Mcond _ -> (Printf.eprintf "Mcond\n"; thereal_transl_instr f i x k)
  | Mjumptable _ -> (Printf.eprintf "Mjumptable\n"; thereal_transl_instr f i x k)
  | Mreturn _ -> (Printf.eprintf "Mreturn\n"; thereal_transl_instr f i x k)
  | _ -> (Printf.eprintf "UNKNOWN\n"; thereal_transl_instr f i x k)
