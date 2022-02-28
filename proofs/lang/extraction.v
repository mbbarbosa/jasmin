Require Import var compiler x86_params.

Require ExtrOcamlBasic.
Require ExtrOcamlString.

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Extraction Inline ssrbool.idP.

Extraction Inline utils.assert.
Extraction Inline utils.Result.bind.

Extract Constant strings.ascii_beq => "Char.equal".
Extract Constant strings.ascii_cmp => "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Extract Constant syscall.syscall_state => "Syscall_ocaml.state".
Extract Constant syscall.get_random => "Syscall_ocaml.get_random".
Extract Constant x86_sem.x86_syscall_sem => "(fun _ _ -> assert false)".
Cd  "lang/ocaml".

Extraction Blacklist String List Nat Utils Var Array.

Separate Extraction var.Sv.fold_var utils sopn expr sem x86_instr_decl x86_params compiler.

Cd  "../..".
