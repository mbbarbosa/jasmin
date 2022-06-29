open Stack_alloc

let pp_pos fmt p =
  Z.pp_print fmt (Conv.z_of_pos p)

let pp_var tbl fmt x =
  Printer.pp_var ~debug:true fmt (Conv.var_of_cvar tbl x)

let rec pp_spexpr fmt e =
  match e with
  | SPconst i -> Z.pp_print fmt (Conv.z_of_cz i)
  | SPbool b -> Format.pp_print_bool fmt b
  | SPvar v -> Format.fprintf fmt "#%a" pp_pos v
  | SPget (aa, ws, x, e) -> Printer.pp_arr_access pp_spexpr pp_spexpr pp_pos fmt aa ws x e None
  | SPsub (aa, ws, len, x, e) -> Printer.pp_arr_access pp_spexpr pp_spexpr pp_pos fmt aa ws x e (Some len)
  | SPapp1 (op, e) -> Format.fprintf fmt "@[<h>(%s@ %a)@]" (Printer.string_of_op1 op) pp_spexpr e
  | SPapp2 (op, e1, e2) -> Format.fprintf fmt "@[(%a %s@ %a)@]" pp_spexpr e1 (Printer.string_of_op2 op) pp_spexpr e2
  | SPappN _ -> assert false
  | SPif _ -> assert false

let pp_region tbl fmt r =
  Format.fprintf fmt "{ slot = %a; wsize = %s; align = %b }"
    (pp_var tbl) r.r_slot
    (Prog.string_of_ws r.r_align)
    r.r_writable

let pp_symbolic_slice fmt s =
  Format.fprintf fmt "[%a:%a]" pp_spexpr s.ss_ofs pp_spexpr s.ss_len

let pp_symbolic_zone fmt z =
  Format.fprintf fmt "@[<h>%a@]" (Format.pp_print_list pp_symbolic_slice) z

let pp_sub_region tbl fmt sr =
  Format.fprintf fmt "{ region = %a; zone = %a }" (pp_region tbl) sr.sr_region pp_symbolic_zone sr.sr_zone

let pp_var_region tbl fmt vr =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sr () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@," (pp_var tbl) (Obj.magic x) (pp_sub_region tbl) sr) vr ();
  Format.fprintf fmt "@]"

let pp_borrowed fmt zs =
  Format.fprintf fmt "@[<v>%a@]" (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_symbolic_zone) zs

let pp_status fmt s =
  let open Region in
  match s with
  | Valid -> Format.fprintf fmt "Valid"
  | Unknown -> Format.fprintf fmt "Unknown"
  | Borrowed zs -> Format.fprintf fmt "Borrowed: %a" pp_borrowed zs

let pp_region_var tbl fmt rv =
  Format.fprintf fmt "@[<v>";
  Mr.fold (fun r sm () ->
    Var0.Mvar.fold (fun x s () ->
      Format.fprintf fmt "%a -> %a -> %a@,"
        (pp_var tbl) (Obj.magic r).r_slot (pp_var tbl) (Obj.magic x)
        pp_status s) sm ()) rv ();
  Format.fprintf fmt "@]"

let pp_rmap tbl fmt rmap =
  let open Region in
  Format.fprintf fmt "@[<v>{ var_region:@;<2 4>%a@;<2 2>region_var:@;<2 4>%a@,}@]@." (pp_var_region tbl) rmap.var_region (pp_region_var tbl) rmap.region_var

let pp_bindings tbl fmt bindings =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sp () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@,"
      (pp_var tbl) (Obj.magic x) pp_spexpr sp) bindings ();
  Format.fprintf fmt "@]"

let pp_table tbl fmt t =
  Format.fprintf fmt "@[<v>{ bindings:@;<2 4>%a@;<2 2>counter: %a@,}@]@." (pp_bindings tbl) t.bindings pp_pos t.counter

