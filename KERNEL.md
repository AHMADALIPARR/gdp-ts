# Kernel

The `Proof` type in `src/index.ts` is a capability witness. A module ran a check and returned a branded object. TypeScript does not inspect the check. That is not a proof, and this fork does not describe it as one.

`src/kernel/check.ts` is the proof checker. A derivation is accepted only when every rule matches the goal and the context. There is no `prove()` and no assertion on the accept path. Rejected certificates return a `CheckError`.

The fragment is propositional natural deduction, plus quantifier-free equality of integer terms decided by normalizing to a constant and variable coefficients. Classical reductio is an explicit rule. Excluded middle is not an axiom. This does not discharge a refinement against a host value, and it is not Liquid Haskell.

The witness layer is unchanged so existing call sites still typecheck. New claims go through `check`.
