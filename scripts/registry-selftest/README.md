# Registry self-test

Test files for the family rule, the `unsafe` rule and the instance column of
`scripts/Registry.lean`. They are not in a Lake library (`lakefile.toml` has no
library under `scripts/`), and the registry scan reads only
`instanceLibraries`. Run them from the project root after a build:

```text
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/SelfTest.lean
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/SelfTest.lean AvailableChainRegistry.Gaps.SelfTest
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/Unsound.lean
```

Each command prints one row per declaration and exits with 0. The expected
statuses:

```text
┌──────────────────────────────────────────┬──────────────────────────────────┬──────────────────────────────┐
│ Declaration                              │ Status                           │ Status with the module       │
│                                          │                                  │ AvailableChainRegistry.Gaps. │
│                                          │                                  │ SelfTest                     │
├──────────────────────────────────────────┼──────────────────────────────────┼──────────────────────────────┤
│ SelfTest.lean: every `neg*` row          │ CONDITIONAL (not a certificate)  │ the same                     │
│ SelfTest.lean: `posGrid`,                │ LEAN (family)                    │ KNOWN-GAP (family)           │
│ `posInstBinder`, `posSA`, `posSapc`      │                                  │                              │
│ SelfTest.lean: `unsafeClosed`            │ UNSOUND(unsafe)                  │ the same                     │
│ SelfTest.lean: `unsafeFamily`            │ UNSOUND(unsafe) (family)         │ the same                     │
│ SelfTest.lean: `fieldCert`               │ LEAN, instance `TwoInst.a`       │ KNOWN-GAP                    │
│ Unsound.lean: `sorryFamily`              │ UNSOUND(sorryAx) (family)        │ not run                      │
└──────────────────────────────────────────┴──────────────────────────────────┴──────────────────────────────┘
```

`posSapc` must also show the instance `AvailableChain.Registry.SAPC.sapcInst`
(the script looks through `toInstance`).

The witness checks need a copy of the script with one changed
`familyBinders` witness. Each copy must exit with 2 and print the message:

```text
┌──────────────────────────────────────────┬────────────────────┬───────────────────────────────────────────┐
│ SA witness in the copy                   │ Run with           │ Message                                   │
├──────────────────────────────────────────┼────────────────────┼───────────────────────────────────────────┤
│ AvailableChain.SA.Tests.pX               │ SelfTest.lean      │ missing witness …                         │
│ AvailableChain.SA.Tests.B (a Block)      │ SelfTest.lean      │ witness … does not have the type …        │
│ RegistrySelfTest.badWitness              │ Unsound.lean       │ witness … uses the axioms [sorryAx]       │
│ RegistrySelfTest.unsafeWitness           │ Unsound.lean       │ witness … is unsafe                       │
└──────────────────────────────────────────┴────────────────────┴───────────────────────────────────────────┘
```

For example, in a scratch directory `$D`:

```text
sed 's/`AvailableChain.SA.Tests.p)/`RegistrySelfTest.unsafeWitness)/' scripts/Registry.lean > $D/RegistryUnsafe.lean
lake env lean --run $D/RegistryUnsafe.lean --selftest scripts/registry-selftest/Unsound.lean
```

`Unsound.lean` uses `sorry` on purpose, so Lean prints `declaration uses
sorry` warnings.
