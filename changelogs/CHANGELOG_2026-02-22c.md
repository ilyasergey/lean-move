# Changelog — 2026-02-22c

## Add standalone MoveLight AST pretty-printer

### Summary

Added `LeanMove/Lang/PrettyPrint.lean` — a pretty-printer that converts MoveLight AST
nodes (`FunDef`, `Stmt`, `Expr`, etc.) into readable strings using the macro notation
from `LeanMove.Lang.Macros`.

### Key changes

#### LeanMove/Lang/PrettyPrint.lean (new, 170 lines)
- `ppSite`, `ppVar`, `ppField`, `ppAref`, `ppBorrowingKind`: primitive pretty-printers
- `ppBasicMoveType`, `ppFieldMap`, `ppFieldEntries` (mutual): type pretty-printers
- `ppMoveType`, `ppParamType`: composite type pretty-printers
- `ppBinop`, `ppExprMacro`: expression pretty-printer using macro notation
  (e.g., `copy var_x`, `borrowMutField(s0, .trecord ..., field_f)`, `#0`)
- `ppStmt`: statement pretty-printer with `;;` sequencing and configurable indentation
  (e.g., `(letsite s0 ← copy var_s) ;;`, `(*s4 ::= s5) ;;`, `ret [s1, s3]`)
- `ppBlock`, `ppParam`, `ppLocal`, `ppFunDef`: FunDef pretty-printer
- `ppTranslatedFunDefs`: convenience function for printing parser translation results

#### LeanMove/Lang.lean (+1 line)
- Added `import LeanMove.Lang.PrettyPrint`

### Result

`lake build` succeeds (349 jobs). No regressions.
