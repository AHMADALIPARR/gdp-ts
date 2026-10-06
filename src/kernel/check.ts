/**
 * Trusted kernel. A derivation is a proof only if `check` accepts it.
 * There is no minting function and no type assertion on the accept path.
 *
 * This is natural deduction for propositional formulas, plus a separate
 * quantifier-free equality judgment on integer terms. It is not Liquid
 * Haskell: there is no refinement SMT query and no predicate on a host value.
 */

export type Formula =
  | { readonly tag: "atom"; readonly name: string }
  | { readonly tag: "and"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "or"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "imp"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "not"; readonly body: Formula }
  | { readonly tag: "bot" };

export type Term =
  | { readonly tag: "lit"; readonly value: number }
  | { readonly tag: "var"; readonly name: string }
  | { readonly tag: "add"; readonly left: Term; readonly right: Term }
  | { readonly tag: "neg"; readonly body: Term };

export type Judgment =
  | { readonly tag: "holds"; readonly formula: Formula }
  | { readonly tag: "eq"; readonly left: Term; readonly right: Term };

export type Derivation =
  | { readonly rule: "assume"; readonly index: number }
  | { readonly rule: "and-i"; readonly left: Derivation; readonly right: Derivation }
  | { readonly rule: "and-el"; readonly proof: Derivation }
  | { readonly rule: "and-er"; readonly proof: Derivation }
  | { readonly rule: "imp-i"; readonly body: Derivation }
  | { readonly rule: "imp-e"; readonly fn: Derivation; readonly arg: Derivation }
  | { readonly rule: "or-il"; readonly proof: Derivation }
  | { readonly rule: "or-ir"; readonly proof: Derivation }
  | { readonly rule: "or-e"; readonly proof: Derivation; readonly left: Derivation; readonly right: Derivation }
  | { readonly rule: "not-i"; readonly body: Derivation }
  | { readonly rule: "not-e"; readonly proof: Derivation; readonly contra: Derivation }
  | { readonly rule: "bot-e"; readonly proof: Derivation }
  | { readonly rule: "raa"; readonly body: Derivation }
  | { readonly rule: "eq-norm" };

export type Context = readonly Judgment[];

export class CheckError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "CheckError";
  }
}

function sameFormula(a: Formula, b: Formula): boolean {
  if (a.tag !== b.tag) return false;
  switch (a.tag) {
    case "atom":
      return b.tag === "atom" && a.name === b.name;
    case "bot":
      return true;
    case "not":
      return b.tag === "not" && sameFormula(a.body, b.body);
    case "and":
    case "or":
    case "imp":
      return b.tag === a.tag && sameFormula(a.left, b.left) && sameFormula(a.right, b.right);
  }
}

function holds(judgment: Judgment): Formula | undefined {
  return judgment.tag === "holds" ? judgment.formula : undefined;
}

function normalize(term: Term): { constant: number; coeffs: Map<string, number> } {
  switch (term.tag) {
    case "lit":
      if (!Number.isInteger(term.value)) throw new CheckError("equality is over integers");
      return { constant: term.value, coeffs: new Map() };
    case "var": {
      const coeffs = new Map<string, number>();
      coeffs.set(term.name, 1);
      return { constant: 0, coeffs };
    }
    case "neg": {
      const body = normalize(term.body);
      const coeffs = new Map<string, number>();
      for (const [name, coefficient] of body.coeffs) coeffs.set(name, -coefficient);
      return { constant: -body.constant, coeffs };
    }
    case "add": {
      const left = normalize(term.left);
      const right = normalize(term.right);
      const coeffs = new Map(left.coeffs);
      for (const [name, coefficient] of right.coeffs) coeffs.set(name, (coeffs.get(name) ?? 0) + coefficient);
      for (const [name, coefficient] of coeffs) if (coefficient === 0) coeffs.delete(name);
      return { constant: left.constant + right.constant, coeffs };
    }
  }
}

function sameNormal(left: Term, right: Term): boolean {
  const a = normalize(left);
  const b = normalize(right);
  if (a.constant !== b.constant || a.coeffs.size !== b.coeffs.size) return false;
  for (const [name, coefficient] of a.coeffs) if (b.coeffs.get(name) !== coefficient) return false;
  return true;
}

function expectHolds(goal: Judgment): Formula {
  if (goal.tag !== "holds") throw new CheckError("rule proves a formula, goal is an equality");
  return goal.formula;
}

export function check(context: Context, goal: Judgment, derivation: Derivation): void {
  switch (derivation.rule) {
    case "assume": {
      const assumed = context[derivation.index];
      if (!assumed) throw new CheckError("assumption index out of range");
      if (goal.tag === "holds") {
        const formula = holds(assumed);
        if (!formula || !sameFormula(formula, goal.formula)) throw new CheckError("assumption does not match goal");
        return;
      }
      if (assumed.tag !== "eq" || !sameNormal(assumed.left, goal.left) || !sameNormal(assumed.right, goal.right)) {
        throw new CheckError("equality assumption does not match goal");
      }
      return;
    }
    case "eq-norm": {
      if (goal.tag !== "eq") throw new CheckError("eq-norm proves an equality");
      if (!sameNormal(goal.left, goal.right)) throw new CheckError("terms are not equal");
      return;
    }
    case "and-i": {
      const formula = expectHolds(goal);
      if (formula.tag !== "and") throw new CheckError("and-i requires a conjunction");
      check(context, { tag: "holds", formula: formula.left }, derivation.left);
      check(context, { tag: "holds", formula: formula.right }, derivation.right);
      return;
    }
    case "and-el":
    case "and-er": {
      const formula = expectHolds(goal);
      const proved = infer(context, derivation.proof);
      if (proved.tag !== "holds" || proved.formula.tag !== "and") throw new CheckError("and-elim requires a conjunction");
      const side = derivation.rule === "and-el" ? proved.formula.left : proved.formula.right;
      if (!sameFormula(side, formula)) throw new CheckError("and-elim side does not match goal");
      return;
    }
    case "imp-i": {
      const formula = expectHolds(goal);
      if (formula.tag !== "imp") throw new CheckError("imp-i requires an implication");
      check([{ tag: "holds", formula: formula.left }, ...context], { tag: "holds", formula: formula.right }, derivation.body);
      return;
    }
    case "imp-e": {
      const formula = expectHolds(goal);
      const fn = infer(context, derivation.fn);
      if (fn.tag !== "holds" || fn.formula.tag !== "imp" || !sameFormula(fn.formula.right, formula)) {
        throw new CheckError("imp-e function does not prove this implication");
      }
      check(context, { tag: "holds", formula: fn.formula.left }, derivation.arg);
      return;
    }
    case "or-il":
    case "or-ir": {
      const formula = expectHolds(goal);
      if (formula.tag !== "or") throw new CheckError("or-intro requires a disjunction");
      const side = derivation.rule === "or-il" ? formula.left : formula.right;
      check(context, { tag: "holds", formula: side }, derivation.proof);
      return;
    }
    case "or-e": {
      const formula = expectHolds(goal);
      const proved = infer(context, derivation.proof);
      if (proved.tag !== "holds" || proved.formula.tag !== "or") throw new CheckError("or-e requires a disjunction");
      check([{ tag: "holds", formula: proved.formula.left }, ...context], goal, derivation.left);
      check([{ tag: "holds", formula: proved.formula.right }, ...context], goal, derivation.right);
      return;
    }
    case "not-i": {
      const formula = expectHolds(goal);
      if (formula.tag !== "not") throw new CheckError("not-i requires a negation");
      check([{ tag: "holds", formula: formula.body }, ...context], { tag: "holds", formula: { tag: "bot" } }, derivation.body);
      return;
    }
    case "not-e": {
      if (goal.tag !== "holds" || goal.formula.tag !== "bot") throw new CheckError("not-e proves false");
      const negated = infer(context, derivation.proof);
      if (negated.tag !== "holds" || negated.formula.tag !== "not") throw new CheckError("not-e requires a negation");
      check(context, { tag: "holds", formula: negated.formula.body }, derivation.contra);
      return;
    }
    case "bot-e": {
      expectHolds(goal);
      check(context, { tag: "holds", formula: { tag: "bot" } }, derivation.proof);
      return;
    }
    case "raa": {
      const formula = expectHolds(goal);
      check(
        [{ tag: "holds", formula: { tag: "not", body: formula } }, ...context],
        { tag: "holds", formula: { tag: "bot" } },
        derivation.body,
      );
      return;
    }
  }
}

function infer(context: Context, derivation: Derivation): Judgment {
  switch (derivation.rule) {
    case "assume": {
      const assumed = context[derivation.index];
      if (!assumed) throw new CheckError("assumption index out of range");
      return assumed;
    }
    case "and-el":
    case "and-er": {
      const proved = infer(context, derivation.proof);
      if (proved.tag !== "holds" || proved.formula.tag !== "and") throw new CheckError("and-elim requires a conjunction");
      return { tag: "holds", formula: derivation.rule === "and-el" ? proved.formula.left : proved.formula.right };
    }
    case "imp-e": {
      const fn = infer(context, derivation.fn);
      if (fn.tag !== "holds" || fn.formula.tag !== "imp") throw new CheckError("imp-e requires an implication");
      check(context, { tag: "holds", formula: fn.formula.left }, derivation.arg);
      return { tag: "holds", formula: fn.formula.right };
    }
    default:
      throw new CheckError(`${derivation.rule} is checkable against a goal, not inferable`);
  }
}

export function proves(context: Context, goal: Judgment, derivation: Derivation): boolean {
  try {
    check(context, goal, derivation);
    return true;
  } catch (error) {
    if (error instanceof CheckError) return false;
    throw error;
  }
}
