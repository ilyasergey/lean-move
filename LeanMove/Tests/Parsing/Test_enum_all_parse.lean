/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils

/-! ## Parse Test: All enum .mvir files

Verifies that all enum .mvir files parse and translate successfully.
-/

open LeanMove.Lang.MoveIR.Parser
open LeanMove.Tests.Parsing.TestUtils

-- Accepted enum tests
private def enum_match_src := include_str "../Typechecking/expressivity/accepted/enum_match.mvir"
private def enum_double_unpack_src := include_str "../Typechecking/expressivity/accepted/enum_double_unpack.mvir"
private def enum_valid_ref_unpack_src := include_str "../Typechecking/expressivity/accepted/enum_valid_ref_unpack.mvir"
private def enum_valid_unpack_loop_src := include_str "../Typechecking/expressivity/accepted/enum_valid_unpack_loop.mvir"
private def enum_borrow_field_mutable_src := include_str "../Typechecking/expressivity/accepted/enum_borrow_field_mutable.mvir"
private def enum_two_mutable_unpacks_src := include_str "../Typechecking/expressivity/accepted/enum_two_mutable_unpacks.mvir"
private def enum_variant_factor_src := include_str "../Typechecking/expressivity/accepted/enum_variant_factor.mvir"
private def enum_factor_invalid_src := include_str "../Typechecking/expressivity/accepted/enum_factor_invalid.mvir"
private def enum_imm_borrow_on_mut_invalid_src := include_str "../Typechecking/expressivity/accepted/enum_imm_borrow_on_mut_invalid.mvir"
private def enum_imm_borrow_on_mut_trivial_invalid_src := include_str "../Typechecking/expressivity/accepted/enum_imm_borrow_on_mut_trivial_invalid.mvir"

-- Rejected enum tests
private def enum_borrow_owned_src := include_str "../Typechecking/expressivity/rejected/enum_borrow_owned.mvir"
private def enum_invalid_ref_unpack_src := include_str "../Typechecking/expressivity/rejected/enum_invalid_ref_unpack.mvir"
private def enum_invalid_ref_unpack_loop_src := include_str "../Typechecking/expressivity/rejected/enum_invalid_ref_unpack_loop.mvir"

-- All parse successfully
#guard (parseMvir enum_match_src).isOk
#guard (parseMvir enum_double_unpack_src).isOk
#guard (parseMvir enum_valid_ref_unpack_src).isOk
#guard (parseMvir enum_valid_unpack_loop_src).isOk
#guard (parseMvir enum_borrow_field_mutable_src).isOk
#guard (parseMvir enum_two_mutable_unpacks_src).isOk
#guard (parseMvir enum_variant_factor_src).isOk
#guard (parseMvir enum_factor_invalid_src).isOk
#guard (parseMvir enum_imm_borrow_on_mut_invalid_src).isOk
#guard (parseMvir enum_imm_borrow_on_mut_trivial_invalid_src).isOk
#guard (parseMvir enum_borrow_owned_src).isOk
#guard (parseMvir enum_invalid_ref_unpack_src).isOk
#guard (parseMvir enum_invalid_ref_unpack_loop_src).isOk

-- All translate successfully
#guard (parseAndTranslate enum_match_src).isOk
#guard (parseAndTranslate enum_double_unpack_src).isOk
#guard (parseAndTranslate enum_valid_ref_unpack_src).isOk
#guard (parseAndTranslate enum_valid_unpack_loop_src).isOk
#guard (parseAndTranslate enum_borrow_field_mutable_src).isOk
#guard (parseAndTranslate enum_two_mutable_unpacks_src).isOk
#guard (parseAndTranslate enum_variant_factor_src).isOk
#guard (parseAndTranslate enum_factor_invalid_src).isOk
#guard (parseAndTranslate enum_imm_borrow_on_mut_invalid_src).isOk
#guard (parseAndTranslate enum_imm_borrow_on_mut_trivial_invalid_src).isOk
#guard (parseAndTranslate enum_borrow_owned_src).isOk
#guard (parseAndTranslate enum_invalid_ref_unpack_src).isOk
#guard (parseAndTranslate enum_invalid_ref_unpack_loop_src).isOk

-- Function count checks (parseAndTranslate returns list of (module, fname, FunDef))
#guard (parseAndTranslate enum_match_src).toOption.get!.length == 1
#guard (parseAndTranslate enum_double_unpack_src).toOption.get!.length == 2
#guard (parseAndTranslate enum_valid_ref_unpack_src).toOption.get!.length == 5
#guard (parseAndTranslate enum_valid_unpack_loop_src).toOption.get!.length == 3
#guard (parseAndTranslate enum_borrow_field_mutable_src).toOption.get!.length == 6
#guard (parseAndTranslate enum_two_mutable_unpacks_src).toOption.get!.length == 1
#guard (parseAndTranslate enum_variant_factor_src).toOption.get!.length == 7
#guard (parseAndTranslate enum_factor_invalid_src).toOption.get!.length == 2
#guard (parseAndTranslate enum_imm_borrow_on_mut_invalid_src).toOption.get!.length == 6
#guard (parseAndTranslate enum_imm_borrow_on_mut_trivial_invalid_src).toOption.get!.length == 2
#guard (parseAndTranslate enum_borrow_owned_src).toOption.get!.length == 1
#guard (parseAndTranslate enum_invalid_ref_unpack_src).toOption.get!.length == 10
#guard (parseAndTranslate enum_invalid_ref_unpack_loop_src).toOption.get!.length == 5
