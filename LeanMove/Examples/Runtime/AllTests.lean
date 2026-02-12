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

-- Import example definitions
import LeanMove.Examples.Typechecking.litmus.accepted.borrow_in_loop_fixed_ok
import LeanMove.Examples.Typechecking.litmus.accepted.deref_borrow_field_ok
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
open AssocMap

-- ============================================================
-- 1. borrow_in_loop_fixed_ok
--    Infinite loop — exhausts fuel without runtime error.
-- ============================================================
section
open LeanMove.Examples.BorrowInLoopFixed

#guard (run 100 (initState foo AssocMap.empty [.int 0])).isError

end

-- ============================================================
-- 2. deref_borrow_field_ok
-- ============================================================
section
open LeanMove.Examples

private def moduleFunEnv : AssocMap Id FunDef :=
  AssocMap.insert (AssocMap.insert AssocMap.empty "M.new" M_new) "M.t" M_t

-- M.new(2) returns record {f: 2}
#guard (run 100 (initState M_new moduleFunEnv [.int 2])).getHaltedValues ==
  some [.record [(⟨"f"⟩, .int 2)]]

-- foo() halts (calls M.t inter-procedurally)
#guard (run 100 (initState foo moduleFunEnv [])).isHalted

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

end

-- ============================================================
-- 4. alias_write_after_join — both branches halt
-- ============================================================
section
open LeanMove.Examples.Expressivity.AliasWriteAfterJoin

#guard (run 200 (initState t AssocMap.empty [.bool true])).isHalted
#guard (run 200 (initState t AssocMap.empty [.bool false])).isHalted

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

end

-- ============================================================
-- 7. imm_borrow_after_mut — no params
-- ============================================================
section
open LeanMove.Examples.Expressivity.ImmBorrowAfterMut

#guard (run 200 (initState direct AssocMap.empty [])).isHalted
#guard (run 200 (initState copy_and_freeze AssocMap.empty [])).isHalted

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
