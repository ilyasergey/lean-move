//! Times the old (graph-based) and new (regex-based) reference-safety analyses
//! in isolation, per function, using production-identical per-function setup.

use move_binary_format::file_format::{FunctionDefinitionIndex, IdentifierIndex, TableIndex};
use move_binary_format::CompiledModule;
use move_bytecode_verifier::{control_flow, reference_safety, regex_reference_safety};
use move_bytecode_verifier_meter::dummy::DummyMeter;
use move_vm_config::verifier::VerifierConfig;
use std::collections::HashMap;
use std::time::Instant;

pub struct FunctionTiming {
    pub old_nanos: u128,
    pub new_nanos: u128,
    pub old_ok: bool,
    pub new_ok: bool,
}

/// For each non-native function in `module`, build the production
/// `FunctionContext` (control-flow pass -- NOT timed) and time the old vs new
/// reference-safety analyses in isolation. `DummyMeter` keeps metering overhead
/// out of the measured region so the numbers reflect the analyses themselves.
pub fn time_reference_safety(
    config: &VerifierConfig,
    module: &CompiledModule,
) -> Vec<FunctionTiming> {
    let mut name_def_map: HashMap<IdentifierIndex, FunctionDefinitionIndex> = HashMap::new();
    for (idx, func_def) in module.function_defs().iter().enumerate() {
        let fh = module.function_handle_at(func_def.function);
        name_def_map.insert(fh.name, FunctionDefinitionIndex(idx as u16));
    }

    let mut out = Vec::new();
    for (idx, fdef) in module.function_defs().iter().enumerate() {
        let index = FunctionDefinitionIndex(idx as TableIndex);
        // Native functions have no code to verify.
        let Some(code) = &fdef.code else { continue };
        // Setup shared by both analyses; excluded from the timed region.
        let Ok(function_context) =
            control_flow::verify_function(config, module, index, fdef, code, &mut DummyMeter)
        else {
            continue;
        };

        let t = Instant::now();
        let old = reference_safety::verify(
            config,
            module,
            &function_context,
            &name_def_map,
            &mut DummyMeter,
        );
        let old_nanos = t.elapsed().as_nanos();

        let t = Instant::now();
        let new =
            regex_reference_safety::verify(config, module, &function_context, &mut DummyMeter);
        let new_nanos = t.elapsed().as_nanos();

        out.push(FunctionTiming {
            old_nanos,
            new_nanos,
            old_ok: old.is_ok(),
            new_ok: new.is_ok(),
        });
    }
    out
}
