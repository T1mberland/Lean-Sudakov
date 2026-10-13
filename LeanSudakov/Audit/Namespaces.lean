import LeanSudakov.Audit.PublicAPI
import Lean.Util.CollectAxioms

namespace LeanSudakov.Audit

-- Check ownership from the compiled environment, not the spelling of source declarations.
run_cmd do
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let mut checked : Nat := 0
  let mut checkedModules : Lean.NameSet := {}
  let mut outside : Array Lean.Name := #[]
  for mod in moduleNames do
    unless (`LeanSudakov).isPrefixOf mod do continue
    let some idx := env.getModuleIdx? mod |
      throwError "Missing imported module index for {mod}"
    let some data := env.header.moduleData[idx.toNat]? |
      throwError "Missing compiled module data for {mod}"
    checkedModules := checkedModules.insert mod
    for name in data.constNames do
      -- A generated mathlib helper can also have been realized in an earlier import.
      unless env.getModuleIdxFor? name == some idx do continue
      let userName := Lean.privateToUserName name
      if (`LeanSudakov).isPrefixOf userName then
        unless Lean.isPrivateName name do
          let oldName := userName.replacePrefix `LeanSudakov .anonymous
          if (env.find? oldName).isSome then
            throwError "Global alias or collision for project declaration: {oldName}"
      else
        -- Lean's simplifier realizes this reserved helper in its mathlib parent's namespace.
        unless name == `Set.enumerateCountable.congr_simp &&
            mod == `LeanSudakov.CountableSudakov &&
            (Lean.Meta.congrKindsExt.find? env name).isSome do
          outside := outside.push name
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  for mod in #[`LeanSudakov.Deterministic, `LeanSudakov.LSECalculus,
      `LeanSudakov.GaussianIBP, `LeanSudakov.GaussianVectorIBP,
      `LeanSudakov.SudakovFernique, `LeanSudakov.SudakovFerniqueDrift,
      `LeanSudakov.CountableSudakov, `LeanSudakov.CountableSudakovExtended,
      `LeanSudakov.CountableSudakovDrift] do
    unless checkedModules.contains mod do
      throwError "Namespace audit did not cover mathematical module {mod}"
  unless (env.find? `map_update_prod_pi).isNone do
    throwError "map_update_prod_pi must not be a global declaration"
  unless (env.find? `LeanSudakov.map_update_prod_pi).isSome do
    throwError "Missing namespaced map_update_prod_pi"
  unless outside.isEmpty do
    throwError "Project declarations outside LeanSudakov: {outside}"
  Lean.logInfo m!"Namespace and axiom audit passed for {checked} project declarations."

end LeanSudakov.Audit
