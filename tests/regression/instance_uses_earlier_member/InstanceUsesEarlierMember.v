(** Crane bug: a section-local instance whose methods use a definition made
    before it, and definitions after it whose types name its [Type] field.

    The instance is emitted as a struct after the file module's struct,
    because its methods call the earlier member ([IuMemImpl::empty_st]);
    the later members are declared inside that struct and spell the field
    as [typename StateV<_tcI0>::state], a template not yet declared there:
      error: no template named 'StateV'

    Reduced from Vellvm, [Semantics/Implementations/Memory.v]: [Memory1]
    declares [get_frame_stack : memM Framestack] and friends with
    [typename MemoryModelStateV<_tcI0>::state], while [MemoryModelStateV]'s
    methods call [Memory1::empty_memory_stack]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import instance_uses_earlier_member.IuMemIface instance_uses_earlier_member.IuMemImpl.

#[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

Module InstanceUsesEarlierMember.
  Definition is_one : bool := Nat.eqb (snd (get_size2 empty_st)) 1.
End InstanceUsesEarlierMember.

Crane Extraction "instance_uses_earlier_member" InstanceUsesEarlierMember.
