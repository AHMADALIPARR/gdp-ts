import { test } from "node:test";
import assert from "node:assert/strict";
import { check, proves, type Derivation, type Formula, type Term } from "../src/kernel/check.ts";

const P: Formula = { tag: "atom", name: "P" };
const Q: Formula = { tag: "atom", name: "Q" };
const assume = (index: number): Derivation => ({ rule: "assume", index });

test("implication introduction and elimination", () => {
  const goal: Formula = { tag: "imp", left: P, right: P };
  check([], { tag: "holds", formula: goal }, { rule: "imp-i", body: assume(0) });
  const modus: Derivation = {
    rule: "imp-e",
    fn: assume(0),
    arg: assume(1),
  };
  check(
    [
      { tag: "holds", formula: { tag: "imp", left: P, right: Q } },
      { tag: "holds", formula: P },
    ],
    { tag: "holds", formula: Q },
    modus,
  );
});

test("conjunction is not accepted from one side", () => {
  const goal = { tag: "holds" as const, formula: { tag: "and" as const, left: P, right: Q } };
  assert.equal(proves([{ tag: "holds", formula: P }], goal, { rule: "and-i", left: assume(0), right: assume(0) }), false);
});

test("excluded middle is not an axiom", () => {
  const goal = { tag: "holds" as const, formula: { tag: "or" as const, left: P, right: { tag: "not" as const, body: P } } };
  assert.equal(proves([], goal, { rule: "or-il", proof: assume(0) }), false);
});

test("integer equality is the normal form, not a minted token", () => {
  const x: Term = { tag: "var", name: "x" };
  const left: Term = { tag: "add", left: x, right: { tag: "lit", value: 1 } };
  const right: Term = { tag: "add", left: { tag: "lit", value: 1 }, right: x };
  check([], { tag: "eq", left, right }, { rule: "eq-norm" });
  assert.equal(
    proves([], { tag: "eq", left: x, right: { tag: "lit", value: 1 } }, { rule: "eq-norm" }),
    false,
  );
});
