
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE3analysis CSE2deps CSE2depsproof.
Require Import Lia.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

  Definition eq_sem (eq : equation) (rs : regset) (m : mem) :=
    match eq_op eq with
    | SOp op =>
      match eval_operation genv sp op (rs ## (eq_args eq)) m with
      | Some v => rs # (eq_lhs eq) = v
      | None => False
      end
    | SLoad chunk addr =>
      match
        match eval_addressing genv sp addr rs##(eq_args eq) with
        | Some a => Mem.loadv chunk m a
        | None => None
        end
      with
      | Some dat => rs # (eq_lhs eq) = dat
      | None => rs # (eq_lhs eq) = default_notrap_load_value chunk
      end
    end.
End SOUNDNESS.
