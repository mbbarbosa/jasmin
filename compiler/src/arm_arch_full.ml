open Arch_decl
open Arm_decl

module type Arm_input = sig
  val call_conv : (register, Arm_decl.__, Arm_decl.__, rflag, condt) calling_convention

end

module Arm (Lowering_params : Arm_input) : Arch_full.Core_arch = struct
  type reg = register
  type regx = Arm_decl.__
  type xreg = Arm_decl.__
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.__
  type fresh_vars = Arm_lowering.fresh_vars
  type lowering_options = Arm_lowering.lowering_options

  let asm_e = Arm_extra.arm_extra
  let aparams = Arm_params.arm_params

  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let lowering_vars _ = ()

  let lowering_opt = ()

  let pp_asm = Pp_arm_m4.print_prog

  let analyze _ _ _ = failwith "TODO_ARM analyze"
end
