open Arch_decl
open Utils
open Arm_decl
open Arm_instr_decl

exception InvalidAddress

let arch = arm_decl

let imm_pre = "#"

(* Possible memory accesses in ARMv7-M are:
 * Offset addressing:
 *   - A register and an immediate offset: [<reg>, #<imm>]
 *   - Two registers: [<reg>, <reg>]
 *   - Two registers and a scale: [<reg>, <reg>, LSL #<imm>] *)
let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | Some disp, None, None -> Printf.sprintf "[%s, %s]" base disp
  | None, Some off, None -> Printf.sprintf "[%s, %s]" base off
  | None, Some off, Some scal -> Printf.sprintf "[%s, %s, lsl %s]" base off scal
  | _, _, _ -> raise InvalidAddress

let pp_rip_address (_ : Ssralg.GRing.ComRing.sort) : string =
  failwith "TODO_ARM pp_rip_address"

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)
(* Assembly code lines. *)

type asm_line =
  | LLabel of string
  | LInstr of string * string list

let iwidth = 4

let pp_asm_line fmt ln =
  match ln with
  | LLabel lbl ->
      Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) ->
      Format.fprintf fmt "\t%-*s" iwidth s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)

let pp_asm_lines fmt lns =
  List.iter (Format.fprintf fmt "%a\n%!" pp_asm_line) lns

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let string_of_label name p = Format.sprintf "L%s$%d" name (Conv.int_of_pos p)

let pp_label n lbl = string_of_label n lbl

let pp_remote_label tbl (fn, lbl) =
  string_of_label (Conv.string_of_funname tbl fn) lbl

let pp_register r = Conv.string_of_string0 (arch.toS_r.to_string r)

let pp_register_ext r = Conv.string_of_string0 (arch.toS_rx.to_string r)

let pp_xregister r = Conv.string_of_string0 (arch.toS_x.to_string r)

let pp_condt c = Conv.string_of_string0 (string_of_condt c)

let pp_imm imm = Format.sprintf "%s%s" imm_pre (Z.to_string imm)

let pp_reg_address addr =
  match addr.ad_base with
  | None ->
      raise InvalidAddress
  | Some r ->
      let base = pp_register r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp = if disp = Z.zero then None else Some (Z.to_string disp) in
      let off = omap pp_register addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal = if scal = Z.zero then None else Some (Z.to_string scal) in
      pp_reg_address_aux base disp off scal

let pp_address addr =
  match addr with
  | Areg ra -> pp_reg_address ra
  | Arip r -> pp_rip_address r

let pp_asm_arg arg =
  match arg with
  | Condt _ -> assert false
  | Imm (ws, w) -> pp_imm (Conv.z_of_word ws w)
  | Reg r -> pp_register r
  | Regx r -> pp_register_ext r
  | Addr addr -> pp_address addr
  | XReg r -> pp_xregister r

(* -------------------------------------------------------------------- *)

let pp_set_flags opts = if opts.set_flags then "s" else ""

let pp_is_conditional opts args =
  if opts.is_conditional then
    (* TODO_ARM: We assume the only condition in the argument list is
       the one we need to print. *)
    match List.opick (is_Condt arch) args with
    | Some ct -> Conv.string_of_string0 (string_of_condt ct)
    | None -> failwith "pp_arm_ext invalid args"
  else ""

let rec insert_before_last x xs =
  match xs with
  | [] -> failwith "insert_before_last invalid list"
  | [y] -> [x; y]
  | y :: z :: xs' -> y :: insert_before_last x (z :: xs')

let pp_shift (ARM_op (_, opts)) args =
  match has_shift opts with
  | Some sk ->
      let s = Conv.string_of_string0 (string_of_shift_kind sk) in
      insert_before_last s args
  | None ->
      args

let pp_mnemonic_ext (ARM_op (mn, opts)) args =
  let mn = Conv.string_of_string0 (string_of_arm_mnemonic mn) in
  Format.sprintf "%s%s%s" mn (pp_set_flags opts) (pp_is_conditional opts args)

let pp_syscall (o : Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

let pp_instr tbl fn (_ : Format.formatter) i =
  match i with
  | ALIGN ->
      failwith "TODO_ARM pp_instr align"
  | LABEL lbl ->
      LLabel (pp_label fn lbl)
  | STORELABEL _ ->
      failwith "TODO_ARM pp_instr storelabel"
  | JMP lbl ->
      LInstr ("b", [pp_remote_label tbl lbl])
  | JMPI _ ->
      failwith "TODO_ARM pp_instr jmpi"
  | Jcc (lbl, ct) ->
      let iname = Printf.sprintf "b%s" (pp_condt ct) in
      LInstr (iname, [pp_label fn lbl])
  | JAL _ ->
      failwith "TODO_ARM pp_instr jal"
  | CALL lbl ->
      LInstr ("bl", [pp_remote_label tbl lbl])
  | POPPC ->
      LInstr ("b", [pp_register LR])
  | SysCall op ->
      LInstr ("call", [pp_syscall op])
  | AsmOp (op, args) ->
      let id = instr_desc arm_decl arm_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_mnemonic_ext op args in
      let args = List.map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
      let args = pp_shift op args in
      LInstr (name, args)

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let mangle x = Format.sprintf "_%s" x

let pp_fun tbl fmt fn fd =
  let fn = Conv.string_of_funname tbl fn in
  let pre = if fd.asm_fd_export then [LLabel (mangle fn); LLabel fn] else [] in
  let body = List.map (pp_instr tbl fn fmt) fd.asm_fd_body in
  let pos =
    (* TODO_ARM: Is this correct? *)
    if fd.asm_fd_export then [pp_instr tbl fn fmt POPPC]
    else []
  in
  pre @ body @ pos

let pp_funcs tbl fmt funs = List.concat_map (curry (pp_fun tbl fmt)) funs

let pp_glob (_ : Ssralg.GRing.ComRing.sort) : asm_line list =
  failwith "TODO_ARM pp_glob"

let pp_data globs = List.concat_map pp_glob globs

let pp_prog tbl fmt p =
  let code = pp_funcs tbl fmt p.asm_funcs in
  let data = pp_data p.asm_globs in
  code @ data

let print_instr tbl s fmt i = pp_asm_lines fmt [pp_instr tbl s fmt i]

let print_prog tbl fmt p = pp_asm_lines fmt (pp_prog tbl fmt p)
