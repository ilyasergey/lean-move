/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import LeanMove.Semantics.Smallstep
import LeanMove.Lang.Macros
import LeanMove.Typing.TypeSoundness

-- Import example definitions
import LeanMove.Examples.Typechecking.litmus.accepted.borrow_in_loop_fixed_ok
import LeanMove.Examples.Typechecking.litmus.accepted.deref_borrow_field_ok
import LeanMove.Examples.Typechecking.litmus.accepted.call_rule_ok
import LeanMove.Examples.Typechecking.litmus.accepted.return_param_ref_ok
import LeanMove.Examples.Typechecking.expressivity.accepted.alias_writes
import LeanMove.Examples.Typechecking.expressivity.accepted.alias_write_after_join
import LeanMove.Examples.Typechecking.expressivity.accepted.extension_after_call
import LeanMove.Examples.Typechecking.expressivity.accepted.extension_writes_after_join
import LeanMove.Examples.Typechecking.expressivity.accepted.imm_borrow_after_mut
import LeanMove.Examples.Typechecking.expressivity.accepted.multible_mutable_return_values
import LeanMove.Examples.Typechecking.expressivity.accepted.mutable_borrows_are_not_unique
import LeanMove.Examples.Typechecking.expressivity.accepted.subtree_writes_release

-- Import rejected example definitions
import LeanMove.Examples.Typechecking.litmus.rejected.borrow_in_loop
import LeanMove.Examples.Typechecking.litmus.rejected.dangling_ref
import LeanMove.Examples.Typechecking.litmus.rejected.use_after_move
import LeanMove.Examples.Typechecking.litmus.rejected.uninitialized_var
import LeanMove.Examples.Typechecking.litmus.rejected.deref_non_ref
import LeanMove.Examples.Typechecking.litmus.rejected.unpack_non_record
import LeanMove.Examples.Typechecking.litmus.rejected.borrow_field_non_ref
import LeanMove.Examples.Typechecking.litmus.rejected.return_local_borrow
import LeanMove.Examples.Typechecking.litmus.rejected.return_aliased_mut
import LeanMove.Examples.Typechecking.litmus.rejected.return_mut_with_outstanding_borrow
import LeanMove.Examples.Typechecking.expressivity.rejected.simple_dangling
import LeanMove.Examples.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid
import LeanMove.Examples.Typechecking.expressivity.rejected.imm_borrow_after_mut_fields_invalid
import LeanMove.Examples.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid

/-!
# Runtime Tests for MoveLight Interpreter

Unit tests for all accepted programs using `#guard`.
Each test runs the interpreter and asserts the expected outcome.
-/

open LeanMove.Semantics
open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Typing.TypeSoundness
open AssocMap

-- ============================================================
-- 1. borrow_in_loop_fixed_ok
--    Infinite loop — exhausts fuel without runtime error.
-- ============================================================
section
open LeanMove.Examples.BorrowInLoopFixed

#guard (run 100 (initState foo AssocMap.empty [.int 0])).isError

-- Type soundness: foo never produces a danglingRef error
private theorem borrow_loop_foo_no_danglingRef :
    ∀ n loc, run n (initState foo empty [.int 0]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec foo foo_lenvDec empty empty [.int 0] Heap.empty (by rfl)

end

-- ============================================================
-- 2. deref_borrow_field_ok
-- ============================================================
section
open LeanMove.Examples

private def moduleFunEnv : AssocMap Id FunDef :=
  AssocMap.insert (AssocMap.insert AssocMap.empty "M.new" M_new) "M.t" M_t

private def module_fte : FunTypingEnv :=
  insert (insert empty "M.new" M_new_lenvDec) "M.t" M_t_lenvDec

-- M.new(2) returns record {f: 2}
#guard (run 100 (initState M_new moduleFunEnv [.int 2])).getHaltedValues ==
  some [.record [(⟨"f"⟩, .int 2)]]

-- foo() halts (calls M.t inter-procedurally)
#guard (run 100 (initState foo moduleFunEnv [])).isHalted

-- Type soundness: M_new never produces a danglingRef error
private theorem deref_borrow_M_new_no_danglingRef :
    ∀ n loc, run n (initState M_new moduleFunEnv [.int 2]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec M_new M_new_lenvDec moduleFunEnv module_fte [.int 2] Heap.empty (by rfl)

-- Type soundness: foo never produces a danglingRef error
private theorem deref_borrow_foo_no_danglingRef :
    ∀ n loc, run n (initState foo moduleFunEnv []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec foo foo_lenvDec moduleFunEnv module_fte [] Heap.empty (by rfl)

-- M.t(this: &M.T) — reads field f from immutable ref, halts
private def mtHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42)])

#guard (run 100 (initState M_t moduleFunEnv [.ref mtHeap.2 []] mtHeap.1)).isHalted

-- Type soundness: M_t never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem deref_borrow_M_t_no_danglingRef :
    ∀ n loc, run n (initState M_t moduleFunEnv [.ref mtHeap.2 []] mtHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec M_t M_t_lenvDec moduleFunEnv module_fte [.ref mtHeap.2 []] mtHeap.1 (by rfl)

end

-- ============================================================
-- 2b. call_rule_ok — call rule accepted tests
-- ============================================================
section
open LeanMove.Examples.Litmus.CallRuleOk

-- Runtime funEnvs (map fn name → FunDef for the interpreter)
private def derefFunEnvRT : AssocMap Id FunDef :=
  AssocMap.insert AssocMap.empty "deref" fn_deref

private def idMutFunEnvRT : AssocMap Id FunDef :=
  AssocMap.insert AssocMap.empty "id_mut" fn_id_mut

-- FunTypingEnvs (map fn name → LabelEnvDec for the type checker)
private def derefFte : FunTypingEnv :=
  insert empty "deref" fn_deref_lenvDec

private def idMutFte : FunTypingEnv :=
  insert empty "id_mut" fn_id_mut_lenvDec

-- basic_return_then_write() halts
#guard (run 200 (initState basic_return_then_write derefFunEnvRT [])).isHalted

-- read_call_output() halts
#guard (run 200 (initState read_call_output idMutFunEnvRT [])).isHalted

-- Type soundness: basic_return_then_write never produces a danglingRef error
private theorem basic_return_no_danglingRef :
    ∀ n loc, run n (initState basic_return_then_write derefFunEnvRT []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec basic_return_then_write basic_return_then_write_lenvDec derefFunEnvRT derefFte [] Heap.empty (by rfl)

-- Type soundness: read_call_output never produces a danglingRef error
private theorem read_call_output_no_danglingRef :
    ∀ n loc, run n (initState read_call_output idMutFunEnvRT []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec read_call_output read_call_output_lenvDec idMutFunEnvRT idMutFte [] Heap.empty (by rfl)

end

-- ============================================================
-- 3. alias_writes — 4 functions, all halt
-- ============================================================
section
open LeanMove.Examples.Expressivity.AliasWrites

#guard (run 200 (initState borrow_local_twice AssocMap.empty [])).isHalted
#guard (run 200 (initState borrow_local_twice_reverse AssocMap.empty [])).isHalted
#guard (run 200 (initState borrow_local_and_copy_ref AssocMap.empty [])).isHalted
#guard (run 200 (initState borrow_local_and_copy_ref_reverse AssocMap.empty [])).isHalted

-- Type soundness: all four alias_writes functions never produce danglingRef errors
private theorem borrow_local_twice_no_danglingRef :
    ∀ n loc, run n (initState borrow_local_twice empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec borrow_local_twice borrow_local_twice_lenvDec empty empty [] Heap.empty (by rfl)

private theorem borrow_local_twice_reverse_no_danglingRef :
    ∀ n loc, run n (initState borrow_local_twice_reverse empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec borrow_local_twice_reverse borrow_local_twice_reverse_lenvDec empty empty [] Heap.empty (by rfl)

private theorem borrow_local_and_copy_ref_no_danglingRef :
    ∀ n loc, run n (initState borrow_local_and_copy_ref empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec borrow_local_and_copy_ref borrow_local_and_copy_ref_lenvDec empty empty [] Heap.empty (by rfl)

private theorem borrow_local_and_copy_ref_reverse_no_danglingRef :
    ∀ n loc, run n (initState borrow_local_and_copy_ref_reverse empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec borrow_local_and_copy_ref_reverse borrow_local_and_copy_ref_reverse_lenvDec empty empty [] Heap.empty (by rfl)

end

-- ============================================================
-- 4. alias_write_after_join — both branches halt
-- ============================================================
section
open LeanMove.Examples.Expressivity.AliasWriteAfterJoin

#guard (run 200 (initState t AssocMap.empty [.bool true])).isHalted
#guard (run 200 (initState t AssocMap.empty [.bool false])).isHalted

-- Type soundness: t never produces a danglingRef error (for any boolean argument)
private theorem alias_write_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool true]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool true] Heap.empty (by rfl)

private theorem alias_write_join_t_false_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool false]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool false] Heap.empty (by rfl)

end

-- ============================================================
-- 5. extension_after_call — ref-param functions
-- ============================================================
section
open LeanMove.Examples.Expressivity.ExtensionAfterCall

private def boxHeap : Heap × Loc :=
  Heap.empty.alloc (.record [
    (⟨"tl"⟩, .record [(⟨"x"⟩, .int 1), (⟨"y"⟩, .int 2)]),
    (⟨"br"⟩, .record [(⟨"x"⟩, .int 3), (⟨"y"⟩, .int 4)])])

#guard (run 100 (initState fn_borrow AssocMap.empty [.ref boxHeap.2 []] boxHeap.1)).isHalted
#guard (run 200 (initState fn_write AssocMap.empty [.ref boxHeap.2 []] boxHeap.1)).isHalted

-- Type soundness: fn_borrow never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem fn_borrow_no_danglingRef :
    ∀ n loc, run n (initState fn_borrow empty [.ref boxHeap.2 []] boxHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fn_borrow fn_borrow_lenvDec empty empty [.ref boxHeap.2 []] boxHeap.1 (by rfl)

-- Type soundness: fn_write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem fn_write_no_danglingRef :
    ∀ n loc, run n (initState fn_write empty [.ref boxHeap.2 []] boxHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fn_write fn_write_lenvDec empty empty [.ref boxHeap.2 []] boxHeap.1 (by rfl)

end

-- ============================================================
-- 6. extension_writes_after_join — bool + two ref params
-- ============================================================
section
open LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin

private def twoStructsHeap : Heap × Loc × Loc :=
  let s := Value.record [(⟨"f"⟩, .int 42)]
  let (h1, l1) := Heap.empty.alloc s
  let (h2, l2) := h1.alloc s
  (h2, l1, l2)

#guard (run 200 (initState t AssocMap.empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1)).isHalted
#guard (run 200 (initState t AssocMap.empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1)).isHalted

private theorem ext_writes_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1 (by rfl)

private theorem ext_writes_join_t_false_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1 (by rfl)

end

-- ============================================================
-- 7. imm_borrow_after_mut — no params
-- ============================================================
section
open LeanMove.Examples.Expressivity.ImmBorrowAfterMut

#guard (run 200 (initState direct AssocMap.empty [])).isHalted
#guard (run 200 (initState copy_and_freeze AssocMap.empty [])).isHalted

-- Type soundness: both functions never produce danglingRef errors
private theorem direct_no_danglingRef :
    ∀ n loc, run n (initState direct empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec direct direct_lenvDec empty empty [] Heap.empty (by rfl)

private theorem copy_and_freeze_no_danglingRef :
    ∀ n loc, run n (initState copy_and_freeze empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec copy_and_freeze copy_and_freeze_lenvDec empty empty [] Heap.empty (by rfl)

end

-- ============================================================
-- 8. multible_mutable_return_values — ref param
-- ============================================================
section
open LeanMove.Examples.Expressivity.MultipleMutableReturnValues

private def pointHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"x"⟩, .int 10), (⟨"y"⟩, .int 20)])

#guard (run 200 (initState borrow AssocMap.empty [.ref pointHeap.2 []] pointHeap.1)).isHalted
#guard (run 200 (initState write AssocMap.empty [.ref pointHeap.2 []] pointHeap.1)).isHalted

-- Type soundness: borrow never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem borrow_no_danglingRef :
    ∀ n loc, run n (initState borrow empty [.ref pointHeap.2 []] pointHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec borrow borrow_lenvDec empty empty [.ref pointHeap.2 []] pointHeap.1 (by rfl)

-- Type soundness: write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem write_no_danglingRef :
    ∀ n loc, run n (initState write empty [.ref pointHeap.2 []] pointHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec write write_lenvDec empty empty [.ref pointHeap.2 []] pointHeap.1 (by rfl)

end

-- ============================================================
-- 9. mutable_borrows_are_not_unique — ref param
-- ============================================================
section
open LeanMove.Examples.Expressivity.MutableBorrowsNotUnique

private def pairHeap : Heap × Loc :=
  Heap.empty.alloc (.record [
    (⟨"s1"⟩, .record [(⟨"f"⟩, .int 1)]),
    (⟨"s2"⟩, .record [(⟨"f"⟩, .int 2)])])

#guard (run 300 (initState fields AssocMap.empty [.ref pairHeap.2 []] pairHeap.1)).isHalted
#guard (run 500 (initState fields_write AssocMap.empty [.ref pairHeap.2 []] pairHeap.1)).isHalted

-- Type soundness: fields never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 8192 in
private theorem fields_no_danglingRef :
    ∀ n loc, run n (initState fields empty [.ref pairHeap.2 []] pairHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fields fields_lenvDec empty empty [.ref pairHeap.2 []] pairHeap.1 (by rfl)

-- Type soundness: fields_write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 8192 in
private theorem fields_write_no_danglingRef :
    ∀ n loc, run n (initState fields_write empty [.ref pairHeap.2 []] pairHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fields_write fields_write_lenvDec empty empty [.ref pairHeap.2 []] pairHeap.1 (by rfl)

end

-- ============================================================
-- 10. subtree_writes_release — bool + ref param
-- ============================================================
section
open LeanMove.Examples.Expressivity.SubtreeWritesRelease

private def treeHeap : Heap × Loc :=
  let s2 (a b : Nat) := Value.record [(⟨"l"⟩, .int a), (⟨"r"⟩, .int b)]
  let s1 (a b c d : Nat) := Value.record [(⟨"l"⟩, s2 a b), (⟨"r"⟩, s2 c d)]
  Heap.empty.alloc (.record [(⟨"l"⟩, s1 1 2 3 4), (⟨"r"⟩, s1 5 6 7 8)])

#guard (run 300 (initState t AssocMap.empty [.bool true, .ref treeHeap.2 []] treeHeap.1)).isHalted
#guard (run 300 (initState t AssocMap.empty [.bool false, .ref treeHeap.2 []] treeHeap.1)).isHalted

-- Type soundness: t never produces a danglingRef error (bool + ref-typed params)
set_option maxRecDepth 16384 in
private theorem subtree_t_true_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool true, .ref treeHeap.2 []] treeHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool true, .ref treeHeap.2 []] treeHeap.1 (by rfl)

set_option maxRecDepth 16384 in
private theorem subtree_t_false_no_danglingRef :
    ∀ n loc, run n (initState t empty [.bool false, .ref treeHeap.2 []] treeHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty [.bool false, .ref treeHeap.2 []] treeHeap.1 (by rfl)

end

-- ============================================================
-- 12. return_param_ref_ok — return reference tests
-- ============================================================
section
open LeanMove.Examples.Litmus.ReturnParamRefOk

-- fn_return_basic(a: u64): u64 — returns basic value, halts
#guard (run 100 (initState fn_return_basic AssocMap.empty [.int 42])).isHalted

-- Type soundness: fn_return_basic never produces a danglingRef error
private theorem fn_return_basic_no_danglingRef :
    ∀ n loc, run n (initState fn_return_basic AssocMap.empty [.int 42]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fn_return_basic fn_return_basic_lenvDec empty empty [.int 42] Heap.empty (by rfl)

-- fn_return_param_ref(r: &mut u64): &mut u64 — returns moved param ref
private def u64Heap : Heap × Loc := Heap.empty.alloc (.int 99)

#guard (run 100 (initState fn_return_param_ref AssocMap.empty [.ref u64Heap.2 []] u64Heap.1)).isHalted

-- Type soundness: fn_return_param_ref never produces a danglingRef error
private theorem fn_return_param_ref_no_danglingRef :
    ∀ n loc, run n (initState fn_return_param_ref AssocMap.empty [.ref u64Heap.2 []] u64Heap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fn_return_param_ref fn_return_param_ref_lenvDec empty empty [.ref u64Heap.2 []] u64Heap.1 (by rfl)

-- fn_return_two(r1: &mut u64, r2: &mut u64): (&mut u64, &mut u64)
private def twoU64Heap : Heap × Loc × Loc :=
  let (h1, l1) := Heap.empty.alloc (.int 1)
  let (h2, l2) := h1.alloc (.int 2)
  (h2, l1, l2)

#guard (run 100 (initState fn_return_two AssocMap.empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1)).isHalted

-- Type soundness: fn_return_two never produces a danglingRef error
private theorem fn_return_two_no_danglingRef :
    ∀ n loc, run n (initState fn_return_two AssocMap.empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec fn_return_two fn_return_two_lenvDec empty empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1 (by rfl)

end

-- ============================================================
-- REJECTED EXAMPLES — runtime evaluation
-- These programs fail type checking but may or may not
-- succeed at runtime.
-- ============================================================

-- ============================================================
-- R1. borrow_in_loop (rejected) — infinite loop
-- ============================================================
section
open LeanMove.Examples.BorrowInLoop

#eval run 100 (initState foo AssocMap.empty [])

end

-- ============================================================
-- R2. simple_dangling — 4 functions
-- ============================================================
section
open LeanMove.Examples.Expressivity.SimpleDangling

-- field_dangling(s: &mut S), S = {f: u64}
private def sHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42)])

#eval run 200 (initState field_dangling AssocMap.empty [.ref sHeap.2 []] sHeap.1)

-- nested_field_dangling(p: &mut P), P = {s: S} = {s: {f: u64}}
private def pHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"s"⟩, .record [(⟨"f"⟩, .int 42)])])

#eval run 200 (initState nested_field_dangling AssocMap.empty [.ref pHeap.2 []] pHeap.1)

-- simple_call_dangling() — no params
#eval run 200 (initState simple_call_dangling AssocMap.empty [])

-- field_call_dangling(s: &mut S)
#eval run 200 (initState field_call_dangling AssocMap.empty [.ref sHeap.2 []] sHeap.1)

end

-- ============================================================
-- R3. imm_borrow_after_mut_call_invalid — no params
-- ============================================================
section
open LeanMove.Examples.Expressivity.ImmBorrowAfterMutCallInvalid

#eval run 200 (initState invalid AssocMap.empty [])

end

-- ============================================================
-- R4. imm_borrow_after_mut_fields_invalid — owned S param
-- ============================================================
section
open LeanMove.Examples.Expressivity.ImmBorrowAfterMutFieldsInvalid

#eval run 200 (initState invalid_write AssocMap.empty [.record [(⟨"f"⟩, .int 42)]])

end

-- ============================================================
-- R5. mutable_borrows_are_not_unique_calls_invalid — &mut S
-- ============================================================
section
open LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid

private def sHeap2 : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42)])

#eval run 200 (initState call_and_write_invalid AssocMap.empty [.ref sHeap2.2 []] sHeap2.1)

end

-- ============================================================
-- R6. dangling_ref — genuine dangling pointer (runtime error!)
--     Field path becomes invalid when parent struct is
--     overwritten with a struct that has different fields.
-- ============================================================
section
open LeanMove.Examples.DanglingRef

-- foo() fails at runtime: readPath on {g:0} with path [field "f"] → none → danglingRef
#eval run 200 (initState foo AssocMap.empty [])

-- Assert it is specifically a danglingRef error
#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.danglingRef _) => true
  | _ => false

end

-- ============================================================
-- R7. use_after_move — ownership violation (uninitializedVar)
-- ============================================================
section
open LeanMove.Examples.UseAfterMove

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.uninitializedVar _) => true
  | _ => false

end

-- ============================================================
-- R8. uninitialized_var — read before assign (uninitializedVar)
-- ============================================================
section
open LeanMove.Examples.UninitializedVar

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.uninitializedVar _) => true
  | _ => false

end

-- ============================================================
-- R9. deref_non_ref — dereference integer (typeMismatch)
-- ============================================================
section
open LeanMove.Examples.DerefNonRef

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.typeMismatch _) => true
  | _ => false

end

-- ============================================================
-- R10. unpack_non_record — unpack integer (typeMismatch)
-- ============================================================
section
open LeanMove.Examples.UnpackNonRecord

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.typeMismatch _) => true
  | _ => false

end

-- ============================================================
-- R11. borrow_field_non_ref — borrow field from record value
--      (typeMismatch)
-- ============================================================
section
open LeanMove.Examples.BorrowFieldNonRef

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.typeMismatch _) => true
  | _ => false

end
