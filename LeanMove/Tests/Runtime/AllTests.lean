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
import LeanMove.Tests.Typechecking.litmus.accepted.borrow_in_loop_fixed_ok
import LeanMove.Tests.Typechecking.litmus.accepted.deref_borrow_field_ok
import LeanMove.Tests.Typechecking.litmus.accepted.call_rule_ok
import LeanMove.Tests.Typechecking.litmus.accepted.return_param_ref_ok
import LeanMove.Tests.Typechecking.litmus.accepted.sized_int_arith_ok
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_writes
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_write_after_join
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_after_call
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_writes_after_join
import LeanMove.Tests.Typechecking.expressivity.accepted.imm_borrow_after_mut
import LeanMove.Tests.Typechecking.expressivity.accepted.multible_mutable_return_values
import LeanMove.Tests.Typechecking.expressivity.accepted.mutable_borrows_are_not_unique
import LeanMove.Tests.Typechecking.expressivity.accepted.subtree_writes_release

-- Import rejected example definitions
import LeanMove.Tests.Typechecking.litmus.rejected.borrow_in_loop
import LeanMove.Tests.Typechecking.litmus.rejected.dangling_ref
import LeanMove.Tests.Typechecking.litmus.rejected.use_after_move
import LeanMove.Tests.Typechecking.litmus.rejected.uninitialized_var
import LeanMove.Tests.Typechecking.litmus.rejected.deref_non_ref
import LeanMove.Tests.Typechecking.litmus.rejected.unpack_non_record
import LeanMove.Tests.Typechecking.litmus.rejected.borrow_field_non_ref
import LeanMove.Tests.Typechecking.litmus.rejected.return_local_borrow
import LeanMove.Tests.Typechecking.litmus.rejected.return_aliased_mut
import LeanMove.Tests.Typechecking.litmus.rejected.return_mut_with_outstanding_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.simple_dangling
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_fields_invalid
import LeanMove.Tests.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_basic_ops
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_borrow_sequential
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_mut_then_imm_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_dangling_borrow
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_two_mutable_unpacks
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_borrow_field_mutable
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_match
import LeanMove.Tests.Typechecking.litmus.accepted.boolean_ops_ok
import LeanMove.Tests.Typechecking.litmus.accepted.comparison_ops_ok

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
open LeanMove.Tests.BorrowInLoopFixed

#guard (run 100 (initState foo AssocMap.empty [.int 0 .u64])).isError

-- Type soundness: foo never produces a danglingRef error
private theorem borrow_loop_foo_no_danglingRef :
    ∀ n loc, run n (initState foo empty [.int 0 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef foo foo_lenvDec AssocMap.empty empty empty [.int 0 .u64] Heap.empty (by native_decide)

end

-- ============================================================
-- 2. deref_borrow_field_ok
-- ============================================================
section
open LeanMove.Tests

private def moduleFunEnv : AssocMap Id FunDef :=
  AssocMap.insert (AssocMap.insert AssocMap.empty "M.new" M_new) "M.t" M_t

private def module_fte : FunTypingEnv :=
  insert (insert empty "M.new" M_new_lenvDec) "M.t" M_t_lenvDec

-- M.new(2) returns record {f: 2}
#guard (run 100 (initState M_new moduleFunEnv [.int 2 .u64])).getHaltedValues ==
  some [.record [(⟨"f"⟩, .int 2 .u64)]]

-- foo() halts (calls M.t inter-procedurally)
#guard (run 100 (initState foo moduleFunEnv [])).isHalted

-- Type soundness: M_new never produces a danglingRef error
private theorem deref_borrow_M_new_no_danglingRef :
    ∀ n loc, run n (initState M_new moduleFunEnv [.int 2 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef M_new M_new_lenvDec AssocMap.empty moduleFunEnv module_fte [.int 2 .u64] Heap.empty (by native_decide)

-- Type soundness: foo never produces a danglingRef error
private theorem deref_borrow_foo_no_danglingRef :
    ∀ n loc, run n (initState foo moduleFunEnv []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef foo foo_lenvDec AssocMap.empty moduleFunEnv module_fte [] Heap.empty (by native_decide)

-- M.t(this: &M.T) — reads field f from immutable ref, halts
private def mtHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42 .u64)])

#guard (run 100 (initState M_t moduleFunEnv [.ref mtHeap.2 []] mtHeap.1)).isHalted

-- Type soundness: M_t never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem deref_borrow_M_t_no_danglingRef :
    ∀ n loc, run n (initState M_t moduleFunEnv [.ref mtHeap.2 []] mtHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef M_t M_t_lenvDec AssocMap.empty moduleFunEnv module_fte [.ref mtHeap.2 []] mtHeap.1 (by native_decide)

end

-- ============================================================
-- 2b. call_rule_ok — call rule accepted tests
-- ============================================================
section
open LeanMove.Tests.Litmus.CallRuleOk

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
  type_soundness_dec_no_danglingRef basic_return_then_write basic_return_then_write_lenvDec AssocMap.empty derefFunEnvRT derefFte [] Heap.empty (by native_decide)

-- Type soundness: read_call_output never produces a danglingRef error
private theorem read_call_output_no_danglingRef :
    ∀ n loc, run n (initState read_call_output idMutFunEnvRT []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef read_call_output read_call_output_lenvDec AssocMap.empty idMutFunEnvRT idMutFte [] Heap.empty (by native_decide)

end

-- ============================================================
-- 3. alias_writes — 4 functions, all halt
-- ============================================================
section
open LeanMove.Tests.Expressivity.AliasWrites

#guard (run 200 (initState parsed_borrow_local_twice AssocMap.empty [])).isHalted
#guard (run 200 (initState parsed_borrow_local_twice_reverse AssocMap.empty [])).isHalted
#guard (run 200 (initState parsed_borrow_local_and_copy_ref AssocMap.empty [])).isHalted
#guard (run 200 (initState parsed_borrow_local_and_copy_ref_reverse AssocMap.empty [])).isHalted

-- Type soundness: all four alias_writes functions never produce danglingRef errors
private theorem borrow_local_twice_no_danglingRef :
    ∀ n loc, run n (initState parsed_borrow_local_twice empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_borrow_local_twice borrow_local_twice_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

private theorem borrow_local_twice_reverse_no_danglingRef :
    ∀ n loc, run n (initState parsed_borrow_local_twice_reverse empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_borrow_local_twice_reverse borrow_local_twice_reverse_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

private theorem borrow_local_and_copy_ref_no_danglingRef :
    ∀ n loc, run n (initState parsed_borrow_local_and_copy_ref empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_borrow_local_and_copy_ref borrow_local_and_copy_ref_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

private theorem borrow_local_and_copy_ref_reverse_no_danglingRef :
    ∀ n loc, run n (initState parsed_borrow_local_and_copy_ref_reverse empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_borrow_local_and_copy_ref_reverse borrow_local_and_copy_ref_reverse_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

end

-- ============================================================
-- 4. alias_write_after_join — both branches halt
-- ============================================================
section
open LeanMove.Tests.Expressivity.AliasWriteAfterJoin

#guard (run 200 (initState parsed_t AssocMap.empty [.bool true])).isHalted
#guard (run 200 (initState parsed_t AssocMap.empty [.bool false])).isHalted

-- Type soundness: t never produces a danglingRef error (for any boolean argument)
private theorem alias_write_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool true]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool true] Heap.empty (by native_decide)

private theorem alias_write_join_t_false_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool false]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool false] Heap.empty (by native_decide)

end

-- ============================================================
-- 5. extension_after_call — ref-param functions
-- ============================================================
section
open LeanMove.Tests.Expressivity.ExtensionAfterCall

private def boxHeap : Heap × Loc :=
  Heap.empty.alloc (.record [
    (⟨"tl"⟩, .record [(⟨"x"⟩, .int 1 .u64), (⟨"y"⟩, .int 2 .u64)]),
    (⟨"br"⟩, .record [(⟨"x"⟩, .int 3 .u64), (⟨"y"⟩, .int 4 .u64)])])

-- Runtime funEnv: fn_write calls "Tester.borrow", so we need it at runtime
private def borrowFunEnvRT : AssocMap Id FunDef :=
  AssocMap.insert AssocMap.empty "Tester.borrow" parsed_fn_borrow

-- FunTypingEnv: maps "Tester.borrow" to its label env for type checking
private def borrowFte : FunTypingEnv :=
  AssocMap.insert AssocMap.empty "Tester.borrow" fn_borrow_lenvDec

#guard (run 100 (initState parsed_fn_borrow AssocMap.empty [.ref boxHeap.2 []] boxHeap.1)).isHalted
#guard (run 200 (initState parsed_fn_write borrowFunEnvRT [.ref boxHeap.2 []] boxHeap.1)).isHalted

-- Type soundness: fn_borrow never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem fn_borrow_no_danglingRef :
    ∀ n loc, run n (initState parsed_fn_borrow empty [.ref boxHeap.2 []] boxHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_fn_borrow fn_borrow_lenvDec AssocMap.empty empty empty [.ref boxHeap.2 []] boxHeap.1 (by native_decide)

-- Type soundness: fn_write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem fn_write_no_danglingRef :
    ∀ n loc, run n (initState parsed_fn_write borrowFunEnvRT [.ref boxHeap.2 []] boxHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_fn_write fn_write_lenvDec AssocMap.empty borrowFunEnvRT borrowFte [.ref boxHeap.2 []] boxHeap.1 (by native_decide)

end

-- ============================================================
-- 6. extension_writes_after_join — bool + two ref params
-- ============================================================
section
open LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin

private def twoStructsHeap : Heap × Loc × Loc :=
  let s := Value.record [(⟨"f"⟩, .int 42 .u64)]
  let (h1, l1) := Heap.empty.alloc s
  let (h2, l2) := h1.alloc s
  (h2, l1, l2)

#guard (run 200 (initState parsed_t AssocMap.empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1)).isHalted
#guard (run 200 (initState parsed_t AssocMap.empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1)).isHalted

private theorem ext_writes_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool true, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1 (by native_decide)

private theorem ext_writes_join_t_false_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool false, .ref twoStructsHeap.2.1 [], .ref twoStructsHeap.2.2 []] twoStructsHeap.1 (by native_decide)

end

-- ============================================================
-- 7. imm_borrow_after_mut — no params
-- ============================================================
section
open LeanMove.Tests.Expressivity.ImmBorrowAfterMut

#guard (run 200 (initState parsed_direct AssocMap.empty [])).isHalted
#guard (run 200 (initState parsed_copy_and_freeze AssocMap.empty [])).isHalted

-- Type soundness: both functions never produce danglingRef errors
private theorem direct_no_danglingRef :
    ∀ n loc, run n (initState parsed_direct empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_direct direct_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

private theorem copy_and_freeze_no_danglingRef :
    ∀ n loc, run n (initState parsed_copy_and_freeze empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_copy_and_freeze copy_and_freeze_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

end

-- ============================================================
-- 8. multible_mutable_return_values — ref param
-- ============================================================
section
open LeanMove.Tests.Expressivity.MultipleMutableReturnValues

private def pointHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"x"⟩, .int 10 .u64), (⟨"y"⟩, .int 20 .u64)])

-- Runtime function environment: write calls Tester.borrow at runtime
private def rtFunEnv : AssocMap Id FunDef :=
  AssocMap.insert AssocMap.empty "Tester.borrow" parsed_borrow

-- Typing function environment: maps "Tester.borrow" to its label env for soundness
private def rtFte : FunTypingEnv :=
  AssocMap.insert AssocMap.empty "Tester.borrow" borrow_lenvDec

#guard (run 200 (initState parsed_borrow AssocMap.empty [.ref pointHeap.2 []] pointHeap.1)).isHalted
#guard (run 200 (initState parsed_write rtFunEnv [.ref pointHeap.2 []] pointHeap.1)).isHalted

-- Type soundness: borrow never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem borrow_no_danglingRef :
    ∀ n loc, run n (initState parsed_borrow empty [.ref pointHeap.2 []] pointHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_borrow borrow_lenvDec AssocMap.empty empty empty [.ref pointHeap.2 []] pointHeap.1 (by native_decide)

-- Type soundness: write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 4096 in
private theorem write_no_danglingRef :
    ∀ n loc, run n (initState parsed_write rtFunEnv [.ref pointHeap.2 []] pointHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_write write_lenvDec AssocMap.empty rtFunEnv rtFte [.ref pointHeap.2 []] pointHeap.1 (by native_decide)

end

-- ============================================================
-- 9. mutable_borrows_are_not_unique — ref param
-- ============================================================
section
open LeanMove.Tests.Expressivity.MutableBorrowsNotUnique

private def pairHeap : Heap × Loc :=
  Heap.empty.alloc (.record [
    (⟨"s1"⟩, .record [(⟨"f"⟩, .int 1 .u64)]),
    (⟨"s2"⟩, .record [(⟨"f"⟩, .int 2 .u64)])])

#guard (run 300 (initState parsed_fields AssocMap.empty [.ref pairHeap.2 []] pairHeap.1)).isHalted
#guard (run 500 (initState parsed_fields_write AssocMap.empty [.ref pairHeap.2 []] pairHeap.1)).isHalted

-- Type soundness: fields never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 8192 in
private theorem fields_no_danglingRef :
    ∀ n loc, run n (initState parsed_fields empty [.ref pairHeap.2 []] pairHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_fields fields_lenvDec AssocMap.empty empty empty [.ref pairHeap.2 []] pairHeap.1 (by native_decide)

-- Type soundness: fields_write never produces a danglingRef error (ref-typed param)
set_option maxRecDepth 8192 in
private theorem fields_write_no_danglingRef :
    ∀ n loc, run n (initState parsed_fields_write empty [.ref pairHeap.2 []] pairHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_fields_write fields_write_lenvDec AssocMap.empty empty empty [.ref pairHeap.2 []] pairHeap.1 (by native_decide)

end

-- ============================================================
-- 10. subtree_writes_release — bool + ref param
-- ============================================================
section
open LeanMove.Tests.Expressivity.SubtreeWritesRelease

private def treeHeap : Heap × Loc :=
  let s2 (a b : Nat) := Value.record [(⟨"l"⟩, .int a .u64), (⟨"r"⟩, .int b .u64)]
  let s1 (a b c d : Nat) := Value.record [(⟨"l"⟩, s2 a b), (⟨"r"⟩, s2 c d)]
  Heap.empty.alloc (.record [(⟨"l"⟩, s1 1 2 3 4), (⟨"r"⟩, s1 5 6 7 8)])

#guard (run 300 (initState parsed_t AssocMap.empty [.bool true, .ref treeHeap.2 []] treeHeap.1)).isHalted
#guard (run 300 (initState parsed_t AssocMap.empty [.bool false, .ref treeHeap.2 []] treeHeap.1)).isHalted

-- Type soundness: t never produces a danglingRef error (bool + ref-typed params)
set_option maxRecDepth 16384 in
private theorem subtree_t_true_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool true, .ref treeHeap.2 []] treeHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool true, .ref treeHeap.2 []] treeHeap.1 (by native_decide)

set_option maxRecDepth 16384 in
private theorem subtree_t_false_no_danglingRef :
    ∀ n loc, run n (initState parsed_t empty [.bool false, .ref treeHeap.2 []] treeHeap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t t_lenvDec AssocMap.empty empty empty [.bool false, .ref treeHeap.2 []] treeHeap.1 (by native_decide)

end

-- ============================================================
-- 12. return_param_ref_ok — return reference tests
-- ============================================================
section
open LeanMove.Tests.Litmus.ReturnParamRefOk

-- fn_return_basic(a: u64): u64 — returns basic value, halts
#guard (run 100 (initState fn_return_basic AssocMap.empty [.int 42 .u64])).isHalted

-- Type soundness: fn_return_basic never produces a danglingRef error
private theorem fn_return_basic_no_danglingRef :
    ∀ n loc, run n (initState fn_return_basic AssocMap.empty [.int 42 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_return_basic fn_return_basic_lenvDec AssocMap.empty empty empty [.int 42 .u64] Heap.empty (by native_decide)

-- fn_return_param_ref(r: &mut u64): &mut u64 — returns moved param ref
private def u64Heap : Heap × Loc := Heap.empty.alloc (.int 99 .u64)

#guard (run 100 (initState fn_return_param_ref AssocMap.empty [.ref u64Heap.2 []] u64Heap.1)).isHalted

-- Type soundness: fn_return_param_ref never produces a danglingRef error
private theorem fn_return_param_ref_no_danglingRef :
    ∀ n loc, run n (initState fn_return_param_ref AssocMap.empty [.ref u64Heap.2 []] u64Heap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_return_param_ref fn_return_param_ref_lenvDec AssocMap.empty empty empty [.ref u64Heap.2 []] u64Heap.1 (by native_decide)

-- fn_return_two(r1: &mut u64, r2: &mut u64): (&mut u64, &mut u64)
private def twoU64Heap : Heap × Loc × Loc :=
  let (h1, l1) := Heap.empty.alloc (.int 1 .u64)
  let (h2, l2) := h1.alloc (.int 2 .u64)
  (h2, l1, l2)

#guard (run 100 (initState fn_return_two AssocMap.empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1)).isHalted

-- Type soundness: fn_return_two never produces a danglingRef error
private theorem fn_return_two_no_danglingRef :
    ∀ n loc, run n (initState fn_return_two AssocMap.empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_return_two fn_return_two_lenvDec AssocMap.empty empty empty [.ref twoU64Heap.2.1 [], .ref twoU64Heap.2.2 []] twoU64Heap.1 (by native_decide)

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
open LeanMove.Tests.BorrowInLoop

#eval run 100 (initState foo AssocMap.empty [])

end

-- ============================================================
-- R2. simple_dangling — 4 functions
-- ============================================================
section
open LeanMove.Tests.Expressivity.SimpleDangling

-- field_dangling(s: &mut S), S = {f: u64}
private def sHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42 .u64)])

#eval run 200 (initState parsed_field_t AssocMap.empty [.ref sHeap.2 []] sHeap.1)

-- nested_field_dangling(p: &mut P), P = {s: S} = {s: {f: u64}}
private def pHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"s"⟩, .record [(⟨"f"⟩, .int 42 .u64)])])

#eval run 200 (initState parsed_nested_field_t AssocMap.empty [.ref pHeap.2 []] pHeap.1)

-- simple_call_dangling() — no params
#eval run 200 (initState parsed_simple_call_t AssocMap.empty [])

-- field_call_dangling(s: &mut S)
#eval run 200 (initState parsed_field_call_t AssocMap.empty [.ref sHeap.2 []] sHeap.1)

end

-- ============================================================
-- R3. imm_borrow_after_mut_call_invalid — no params
-- ============================================================
section
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid

#eval run 200 (initState parsed_invalid AssocMap.empty [])

end

-- ============================================================
-- R4. imm_borrow_after_mut_fields_invalid — owned S param
-- ============================================================
section
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutFieldsInvalid

#eval run 200 (initState parsed_invalid_write AssocMap.empty [.record [(⟨"f"⟩, .int 42 .u64)]])

end

-- ============================================================
-- R5. mutable_borrows_are_not_unique_calls_invalid — &mut S
-- ============================================================
section
open LeanMove.Tests.Expressivity.MutableBorrowsNotUniqueCallsInvalid

private def sHeap2 : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42 .u64)])

-- Runtime function environment: call_and_write_invalid calls borrow_f
private def rtFunEnv2 : AssocMap Id FunDef :=
  AssocMap.insert AssocMap.empty "borrow_f" parsed_borrow_f

#eval run 200 (initState parsed_call_and_write_invalid rtFunEnv2 [.ref sHeap2.2 []] sHeap2.1)

end

-- ============================================================
-- R6. dangling_ref — genuine dangling pointer (runtime error!)
--     Field path becomes invalid when parent struct is
--     overwritten with a struct that has different fields.
-- ============================================================
section
open LeanMove.Tests.DanglingRef

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
open LeanMove.Tests.UseAfterMove

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.uninitializedVar _) => true
  | _ => false

end

-- ============================================================
-- R8. uninitialized_var — read before assign (uninitializedVar)
-- ============================================================
section
open LeanMove.Tests.UninitializedVar

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.uninitializedVar _) => true
  | _ => false

end

-- ============================================================
-- R9. deref_non_ref — dereference integer (typeMismatch)
-- ============================================================
section
open LeanMove.Tests.DerefNonRef

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.typeMismatch _) => true
  | _ => false

end

-- ============================================================
-- R10. unpack_non_record — unpack integer (typeMismatch)
-- ============================================================
section
open LeanMove.Tests.UnpackNonRecord

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
open LeanMove.Tests.BorrowFieldNonRef

#eval run 200 (initState foo AssocMap.empty [])

#guard match run 200 (initState foo AssocMap.empty []) with
  | .error (.typeMismatch _) => true
  | _ => false

end

-- ============================================================
-- V1. vec_pack_empty — pack empty vector, return it
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

#eval run 200 (initState parsed_vec_pack_empty AssocMap.empty [])

#guard (run 200 (initState parsed_vec_pack_empty AssocMap.empty [])).getHaltedValues ==
  some [.vec .u64 []]

end

-- ============================================================
-- V2. vec_pack_elems — pack elements into vector, return it
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

#eval run 200 (initState parsed_vec_pack_elems AssocMap.empty [])

#guard (run 200 (initState parsed_vec_pack_elems AssocMap.empty [])).getHaltedValues ==
  some [.vec .u64 [.int 0 .u64, .int 1 .u64]]

end

-- ============================================================
-- V3. vec_len — get vector length
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

private def vecLenHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 10 .u64, .int 20 .u64, .int 30 .u64])

#eval run 200 (initState parsed_vec_len AssocMap.empty [.ref vecLenHeap.2 []] vecLenHeap.1)

#guard (run 200 (initState parsed_vec_len AssocMap.empty [.ref vecLenHeap.2 []] vecLenHeap.1)).getHaltedValues ==
  some [.int 3 .u64]

end

-- ============================================================
-- V4. vec_push — push element to vector
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

private def vecPushHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 10 .u64])

#eval run 200 (initState parsed_vec_push AssocMap.empty [.ref vecPushHeap.2 []] vecPushHeap.1)

#guard (run 200 (initState parsed_vec_push AssocMap.empty [.ref vecPushHeap.2 []] vecPushHeap.1)).isHalted

end

-- ============================================================
-- V5. vec_pop — pop element from vector
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

private def vecPopHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 10 .u64, .int 20 .u64, .int 30 .u64])

#eval run 200 (initState parsed_vec_pop AssocMap.empty [.ref vecPopHeap.2 []] vecPopHeap.1)

#guard (run 200 (initState parsed_vec_pop AssocMap.empty [.ref vecPopHeap.2 []] vecPopHeap.1)).getHaltedValues ==
  some [.int 30 .u64]

end

-- ============================================================
-- V6. vec_imm_borrow_read — immutable element borrow, read
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBorrowSequential

private def vecBorrowHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 42 .u64, .int 99 .u64])

#eval run 200 (initState parsed_vec_imm_borrow_read AssocMap.empty [.ref vecBorrowHeap.2 []] vecBorrowHeap.1)

#guard (run 200 (initState parsed_vec_imm_borrow_read AssocMap.empty [.ref vecBorrowHeap.2 []] vecBorrowHeap.1)).getHaltedValues ==
  some [.int 42 .u64]

end

-- ============================================================
-- V7. vec_mut_borrow_write — mutable element borrow, write 99
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBorrowSequential

private def vecMutBorrowHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 0 .u64, .int 0 .u64])

#eval run 200 (initState parsed_vec_mut_borrow_write AssocMap.empty [.ref vecMutBorrowHeap.2 []] vecMutBorrowHeap.1)

#guard (run 200 (initState parsed_vec_mut_borrow_write AssocMap.empty [.ref vecMutBorrowHeap.2 []] vecMutBorrowHeap.1)).isHalted

end

-- ============================================================
-- V1s. vec_pack_empty — type soundness
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

private theorem vec_pack_empty_no_danglingRef :
    ∀ n loc, run n (initState parsed_vec_pack_empty AssocMap.empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_vec_pack_empty vec_pack_empty_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

end

-- ============================================================
-- V2s. vec_pack_elems — type soundness
-- ============================================================
section
open LeanMove.Tests.Expressivity.VecBasicOps

private theorem vec_pack_elems_no_danglingRef :
    ∀ n loc, run n (initState parsed_vec_pack_elems AssocMap.empty []) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_vec_pack_elems vec_pack_elems_lenvDec AssocMap.empty empty empty [] Heap.empty (by native_decide)

end

-- ============================================================
-- E1. enum_borrow_field_mutable M2.baz — runtime + type soundness
--     (takes &mut u64, which hasType_bool handles)
-- ============================================================
section
open LeanMove.Tests.Expressivity.EnumBorrowFieldMutable

-- Heap with a u64 value
private def bazHeap : Heap × Loc :=
  Heap.empty.alloc (.int 42 .u64)

#eval run 200 (initState parsed_M2_baz AssocMap.empty [.ref bazHeap.2 []] bazHeap.1)

#guard (run 200 (initState parsed_M2_baz AssocMap.empty [.ref bazHeap.2 []] bazHeap.1)).isHalted

-- Type soundness: M2.baz never produces a danglingRef error
set_option maxRecDepth 4096 in
private theorem enum_M2_baz_no_danglingRef :
    ∀ n loc, run n (initState parsed_M2_baz AssocMap.empty [.ref bazHeap.2 []] bazHeap.1 (enumEnv := enumEnv)) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_M2_baz M2_baz_lenvDec enumEnv empty empty [.ref bazHeap.2 []] bazHeap.1 (by native_decide)

end

-- ============================================================
-- E2. enum_match — runtime (variant_switch dispatch)
--     t0() packs Threes.Three{pos0: 0}, switches, returns 0
-- ============================================================
section
open LeanMove.Tests.Expressivity.EnumMatch

#eval run 200 (initState parsed_t0 AssocMap.empty [] (enumEnv := enumEnv))

#guard (run 200 (initState parsed_t0 AssocMap.empty [] (enumEnv := enumEnv))).getHaltedValues ==
  some [.int 0 .u64]

-- Decidable type soundness for a multi-variant enum (3 variants: One, Two, Three)
set_option maxRecDepth 4096 in
private theorem enum_match_no_danglingRef :
    ∀ n loc, run n (initState parsed_t0 AssocMap.empty [] (enumEnv := enumEnv)) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef parsed_t0 t0_lenvDec enumEnv empty empty [] Heap.empty (by native_decide)

end

-- ============================================================
-- E3. enum_two_mutable_unpacks — runtime only
--     (takes &mut Self.Foo; checkArgsCompatible doesn't handle variant values yet)
-- ============================================================
section
open LeanMove.Tests.Expressivity.EnumTwoMutableUnpacks

-- Heap with a Foo.V { a: 10, b: 20 } variant
private def fooHeap : Heap × Loc :=
  Heap.empty.alloc (.variant "V" "M.Foo" [(⟨"a"⟩, .int 10 .u64), (⟨"b"⟩, .int 20 .u64)])

#eval run 200 (initState parsed_fn AssocMap.empty [.ref fooHeap.2 []] fooHeap.1)

#guard (run 200 (initState parsed_fn AssocMap.empty [.ref fooHeap.2 []] fooHeap.1)).isHalted

end

-- ============================================================
-- B1. boolean_ops_ok — runtime (And, Or, Not)
--     Exercises evalBinopBool and evalUnop, which the typechecking
--     litmus tests only type and never execute.
-- ============================================================
section
open LeanMove.Tests.Litmus.BooleanOpsOk

-- !((a == b) && (a < b)) || (a == b): the conjunction is unsatisfiable, so the
-- negation — and hence the disjunction — holds for every a, b.
#guard (run 100 (initState fn_and_or_not AssocMap.empty [.int 2 .u64, .int 7 .u64])).getHaltedValues ==
  some [.bool true]
#guard (run 100 (initState fn_and_or_not AssocMap.empty [.int 3 .u64, .int 3 .u64])).getHaltedValues ==
  some [.bool true]

-- !!(a == b)
#guard (run 100 (initState fn_double_negation AssocMap.empty [.int 2 .u64, .int 7 .u64])).getHaltedValues ==
  some [.bool false]
#guard (run 100 (initState fn_double_negation AssocMap.empty [.int 3 .u64, .int 3 .u64])).getHaltedValues ==
  some [.bool true]

private theorem boolean_ops_no_danglingRef :
    ∀ n loc, run n (initState fn_and_or_not empty [.int 2 .u64, .int 7 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_and_or_not fn_and_or_not_lenvDec empty empty empty
    [.int 2 .u64, .int 7 .u64] Heap.empty (by native_decide)

end

-- ============================================================
-- B2. comparison_ops_ok — runtime (Neq, Gt, Le, Ge)
--     Exercises the new evalBinop rows.
-- ============================================================
section
open LeanMove.Tests.Litmus.ComparisonOpsOk

-- (a != b && a > b) || (a <= b) && (a >= b)
-- a = 2, b = 7: (T && F) || T = T, then T && F = false
#guard (run 100 (initState fn_comparisons AssocMap.empty [.int 2 .u64, .int 7 .u64])).getHaltedValues ==
  some [.bool false]
-- a = 7, b = 2: (T && T) || F = T, then T && T = true
#guard (run 100 (initState fn_comparisons AssocMap.empty [.int 7 .u64, .int 2 .u64])).getHaltedValues ==
  some [.bool true]

-- Neq at bool
#guard (run 100 (initState fn_neq_bool AssocMap.empty [.bool true, .bool false])).getHaltedValues ==
  some [.bool true]
#guard (run 100 (initState fn_neq_bool AssocMap.empty [.bool true, .bool true])).getHaltedValues ==
  some [.bool false]

-- Ge in branch position: takes b2 (returns a) when a >= b, b1 (returns b) otherwise
#guard (run 100 (initState fn_ge_branch AssocMap.empty [.int 5 .u64, .int 3 .u64])).getHaltedValues ==
  some [.int 5 .u64]
#guard (run 100 (initState fn_ge_branch AssocMap.empty [.int 2 .u64, .int 7 .u64])).getHaltedValues ==
  some [.int 7 .u64]

private theorem comparison_ops_no_danglingRef :
    ∀ n loc, run n (initState fn_comparisons empty [.int 2 .u64, .int 7 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_comparisons fn_comparisons_lenvDec empty empty empty
    [.int 2 .u64, .int 7 .u64] Heap.empty (by native_decide)

set_option maxRecDepth 4096 in
private theorem ge_branch_no_danglingRef :
    ∀ n loc, run n (initState fn_ge_branch empty [.int 5 .u64, .int 3 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_ge_branch fn_ge_branch_lenvDec empty empty empty
    [.int 5 .u64, .int 3 .u64] Heap.empty (by native_decide)

end

-- ============================================================
-- 16. sized_int_arith_ok — width-checked arithmetic at run time
-- ============================================================
section
open LeanMove.Tests.Litmus.SizedIntArithOk

-- Ordinary subtraction halts with the difference.
#guard (run 100 (initState fn_sub empty [.int 5 .u64, .int 3 .u64])).getHaltedValues ==
  some [.int 2 .u64]

-- Underflow aborts. Before widths were tracked this silently produced `.int 0`,
-- because Lean's `Nat` subtraction truncates at zero.
#guard (run 100 (initState fn_sub empty [.int 0 .u64, .int 1 .u64])) matches
  .error .arithmeticError

-- The largest `u8` sum that still fits, and the first one that does not.
#guard (run 100 (initState fn_add_u8 empty [.int 254 .u8, .int 1 .u8])).getHaltedValues ==
  some [.int 255 .u8]
#guard (run 100 (initState fn_add_u8 empty [.int 255 .u8, .int 1 .u8])) matches
  .error .arithmeticError

-- 16 * 16 = 256 overflows a `u8` but is unremarkable at `u64`, so the width
-- really is what decides the abort.
#guard (run 100 (initState fn_mul_u8 empty [.int 16 .u8, .int 16 .u8])) matches
  .error .arithmeticError
#guard (run 100 (initState fn_mul_u8 empty [.int 15 .u8, .int 17 .u8])).getHaltedValues ==
  some [.int 255 .u8]

-- `u256` arithmetic runs on the same code path.
#guard (run 100 (initState fn_add_u256 empty [.int 1 .u256, .int 2 .u256])).getHaltedValues ==
  some [.int 3 .u256]

-- Per-execution soundness certificates. The first two matter most: they are
-- executions that *reach* an arithmetic abort, so they witness that the new
-- error is genuinely accepted rather than vacuously excluded.
private theorem sub_underflow_no_danglingRef :
    ∀ n loc, run n (initState fn_sub empty [.int 0 .u64, .int 1 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_sub fn_sub_lenvDec empty empty empty
    [.int 0 .u64, .int 1 .u64] Heap.empty (by native_decide)

private theorem add_u8_overflow_no_danglingRef :
    ∀ n loc, run n (initState fn_add_u8 empty [.int 255 .u8, .int 1 .u8]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_add_u8 fn_add_u8_lenvDec empty empty empty
    [.int 255 .u8, .int 1 .u8] Heap.empty (by native_decide)

private theorem mul_u8_no_danglingRef :
    ∀ n loc, run n (initState fn_mul_u8 empty [.int 15 .u8, .int 17 .u8]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_mul_u8 fn_mul_u8_lenvDec empty empty empty
    [.int 15 .u8, .int 17 .u8] Heap.empty (by native_decide)

end

-- ============================================================
-- 17. casts — CastU* checks rather than truncates
-- ============================================================
section
open LeanMove.Tests.Litmus.SizedIntArithOk

-- A value that fits the target width passes through unchanged, but comes out
-- at the *new* width — `.int 200 .u8`, not `.int 200 .u64`.
#guard (run 100 (initState fn_narrow empty [.int 200 .u64])).getHaltedValues ==
  some [.int 200 .u8]

-- The boundary: 255 fits a u8, 256 does not.
#guard (run 100 (initState fn_narrow empty [.int 255 .u64])).getHaltedValues ==
  some [.int 255 .u8]
#guard (run 100 (initState fn_narrow empty [.int 256 .u64])) matches
  .error .arithmeticError

-- Widening always succeeds.
#guard (run 100 (initState fn_widen empty [.int 255 .u8])).getHaltedValues ==
  some [.int 255 .u64]

-- Certificates for both the succeeding and the aborting cast.
private theorem narrow_ok_no_danglingRef :
    ∀ n loc, run n (initState fn_narrow empty [.int 200 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_narrow fn_narrow_lenvDec empty empty empty
    [.int 200 .u64] Heap.empty (by native_decide)

private theorem narrow_abort_no_danglingRef :
    ∀ n loc, run n (initState fn_narrow empty [.int 256 .u64]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_narrow fn_narrow_lenvDec empty empty empty
    [.int 256 .u64] Heap.empty (by native_decide)

private theorem widen_no_danglingRef :
    ∀ n loc, run n (initState fn_widen empty [.int 255 .u8]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_widen fn_widen_lenvDec empty empty empty
    [.int 255 .u8] Heap.empty (by native_decide)

end

-- ============================================================
-- 18. bitwise — BitAnd / BitOr / Xor
-- ============================================================
section
open LeanMove.Tests.Litmus.SizedIntArithOk

-- 0b1100 ^ 0b1010 = 0b0110
#guard (run 100 (initState fn_xor_u8 empty [.int 12 .u8, .int 10 .u8])).getHaltedValues ==
  some [.int 6 .u8]

-- Bitwise operations never overflow: the widest possible u8 operands still
-- produce a u8, so unlike `fn_add_u8` this cannot abort.
#guard (run 100 (initState fn_xor_u8 empty [.int 255 .u8, .int 0 .u8])).getHaltedValues ==
  some [.int 255 .u8]
#guard (run 100 (initState fn_xor_u8 empty [.int 255 .u8, .int 255 .u8])).getHaltedValues ==
  some [.int 0 .u8]

private theorem xor_u8_no_danglingRef :
    ∀ n loc, run n (initState fn_xor_u8 empty [.int 255 .u8, .int 255 .u8]) ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef fn_xor_u8 fn_xor_u8_lenvDec empty empty empty
    [.int 255 .u8, .int 255 .u8] Heap.empty (by native_decide)

end
