# Namespace Convention

All project-owned mathematical declarations live in `LeanSudakov`. This includes
finite deterministic inequalities, softmax calculus, Gaussian integration by
parts and covariance algebra, interpolation, and finite/countable comparisons
with or without deterministic drift. These APIs share the same finite-vector
infrastructure, and their existing descriptive names distinguish their roles;
additional per-file namespaces would fragment that shared API unnecessarily.

Verification code lives in `LeanSudakov.Audit`. Private helpers remain private
inside the namespace of their module. Module paths and imports are unchanged.

## Migration

Every previously global public definition, lemma, and theorem `name` is now
`LeanSudakov.name`, with its statement, hypotheses, and mathematical body
unchanged. The migration covers 249 public declarations in nine mathematical
modules; private helpers move with them. For example:

| Previous name | New name |
| --- | --- |
| `vecMax` | `LeanSudakov.vecMax` |
| `lse` | `LeanSudakov.lse` |
| `softmax` | `LeanSudakov.softmax` |
| `hessian_cov_rewrite` | `LeanSudakov.hessian_cov_rewrite` |
| `map_update_prod_pi` | `LeanSudakov.map_update_prod_pi` |
| `gaussian_ibp_softmax` | `LeanSudakov.gaussian_ibp_softmax` |
| `gaussian_interpolation_lse_mono` | `LeanSudakov.gaussian_interpolation_lse_mono` |
| `sudakov_fernique` | `LeanSudakov.sudakov_fernique` |
| `sudakov_fernique_drift` | `LeanSudakov.sudakov_fernique_drift` |
| `countable_sudakov` | `LeanSudakov.countable_sudakov` |
| `countable_sudakov_drift` | `LeanSudakov.countable_sudakov_drift` |

Use fully qualified names after importing `LeanSudakov`, or explicitly opt into
short names with `open LeanSudakov`. There are no global aliases or exports of
the old names; in particular, importing this library no longer declares global
`map_update_prod_pi`.

## Exceptions

There are no exceptions for authored mathematical declarations: none was
already in a mathlib namespace. There is one compiler-generated exception:
Lean's simplifier realizes `Set.enumerateCountable.congr_simp` while compiling
`LeanSudakov.CountableSudakov`. This reserved congruence theorem belongs beside
mathlib's `Set.enumerateCountable`, not in our public API. The namespace audit
allows only that exact name from that exact module, and checks Lean's congruence
registration metadata; its axiom dependencies are still audited.

Existing mathlib declarations remain untouched. A future declaration that
genuinely extends a mathlib structure may use its established namespace, but
that exception must be documented and explicitly audited. Lake package and
library configuration are build declarations, not mathematical API.

## Verification

`lake build` builds the library and all audit modules by default.

- `LeanSudakov.Audit.Finite` and `LeanSudakov.Audit.Countable` retain the existing
  guarded axiom reports and countable edge-case examples under the new names.
- `LeanSudakov.Audit.Namespaces` checks declarations by their originating Lean
  module, including private/generated constants. All project-owned declarations
  must have a `LeanSudakov` prefix (after decoding private names), except for the
  documented generated mathlib helper, and all their axiom dependencies must
  belong to `{propext, Classical.choice, Quot.sound}`.
  It also rejects old global aliases and checks the formerly conflicting name.
- `LeanSudakov.Audit.PublicAPI` compiles fully qualified uses of the public API
  without opening `LeanSudakov`.

`STEIN_PLAN.md` is historical planning material; its short mathematical names
are now interpreted in `LeanSudakov` under this convention.
