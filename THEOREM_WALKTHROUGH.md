# Line-by-line walkthrough of the n = 13 dominance theorem

**Purpose.** This document explains the *statement* of the repository's simplest
dominance theorem, one line at a time, so that a reader who is not a Lean expert
can audit it independently. It covers only the theorem's hypotheses and
conclusion — not its proof.

**Why the statement is the thing to audit.** Lean's kernel has already checked
the proof, and `CheckAxioms.lean` certifies that the proof depends on nothing
but the three standard axioms of Lean/mathlib (`propext`,
`Classical.choice`, `Quot.sound`) — in particular no `sorry` (which would appear
as `sorryAx`) and no `native_decide` (which would appear as
`Lean.ofReduceBool`). So the proof is not where a human check adds value. The
place an error can survive machine checking is the **statement**: a theorem can
typecheck, be genuinely proved, and still not mean what it appears to mean.
That is what this document is for.

**Why this theorem.** It is the smallest complete claim in the repository:
a single concrete case (`n₁ = n₂ = 13`) with a literal rational `ε = 1/2000`,
whose dependency closure is 40 files / ~10,000 lines and contains none of the
general-`n` or unequal-size machinery.

Source: [`GraybillDeal/RawEstimatorRisk.lean:163`](GraybillDeal/RawEstimatorRisk.lean).

---

## The theorem in full

```lean
theorem rawGraybillDealEstimator13_strictly_dominated
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X P μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (fun ω =>
          let r :=
            sampleVariance13 (X 0) ω
              / (sampleVariance13 (X 0) ω
                + sampleVariance13 (X 1) ω)
          let q :=
            13 * meanDifference13 X ω ^ 2
              / (sampleVariance13 (X 0) ω
                + sampleVariance13 (X 1) ω)
          sampleMean13 (X 0) ω
            + clip01
                (r + epsilon13 * r * (1 - r) * (1 - 2 * r) * (4 - q))
              * meanDifference13 X ω) P
      <
    sqRisk μ
        (fun ω =>
          sampleMean13 (X 0) ω
            + (sampleVariance13 (X 0) ω
                / (sampleVariance13 (X 0) ω
                  + sampleVariance13 (X 1) ω))
      * meanDifference13 X ω) P
```

In ordinary notation, with `X̄ᵢ` the sample means, `Sᵢ²` the unbiased sample
variances, `D = X̄₂ − X̄₁`, `r = S₁²/(S₁²+S₂²)`, `q = 13D²/(S₁²+S₂²)`:

> For every common mean `μ ∈ ℝ` and every pair of variances `σ₁², σ₂² > 0`,
>
> `E[(μ̂* − μ)²] < E[(μ̂_GD − μ)²]`
>
> where `μ̂_GD = X̄₁ + D·r` is the Graybill–Deal estimator and
> `μ̂* = X̄₁ + D·clip₀₁(r + (1/2000)·r(1−r)(1−2r)(4−q))`.

A useful reading discipline for what follows: **the binders declare shapes and
assert nothing; the hypotheses carry all the assumptions; the conclusion is a
single inequality between two real numbers.**

---

## 1. The ambient context

Not part of the theorem, but in scope from the top of the file
([`RawEstimatorRisk.lean:27`](GraybillDeal/RawEstimatorRisk.lean)):

```lean
variable {Ω : Type*} [MeasurableSpace Ω]
```

This is a *declaration*, not a definition — `Ω` is never defined anywhere. It is
an arbitrary type, universally quantified, so the theorem holds for **every**
such `Ω`. Two separate things are being supplied:

* `{Ω : Type*}` — `Ω` is a type: the set of outcomes. (`Type*` is universe
  bookkeeping; read it as "some type".)
* `[MeasurableSpace Ω]` — an anonymous typeclass instance carrying the
  σ-algebra. From mathlib's `MeasurableSpace` structure, this is exactly a
  predicate `MeasurableSet' : Set Ω → Prop` plus the three σ-algebra axioms
  (contains `∅`, closed under complement, closed under countable union).

So strictly: `Ω` is a type, and the *measurable space* is the pair of `Ω` with
that instance. Calling `Ω` "a measurable space" is standard shorthand.

There is no measure yet — that arrives in the next line.

**Audit note.** Because the σ-algebra is an inferred instance rather than
written down, it is invisible here. It becomes concrete only when `Ω` is
instantiated, which happens in `ModelWitness.lean` (as `(Fin 2 × Fin 13) → ℝ`
with mathlib's standard product-of-Borel instance). A degenerate σ-algebra would
make the hypotheses unsatisfiable and the theorem vacuous, which is why the
witness file matters.

---

## 2. The data (binders)

### `{X : Fin 2 → Fin 13 → Ω → ℝ}`

The dataset. The arrows associate to the right, so this is *curried* and the
intermediate stages are meaningful:

| expression | type | meaning |
|---|---|---|
| `X` | `Fin 2 → Fin 13 → Ω → ℝ` | the whole dataset |
| `X 0` | `Fin 13 → Ω → ℝ` | the first sample |
| `X 0 5` | `Ω → ℝ` | the 6th observation of sample 1 — **a random variable** |
| `X 0 5 ω` | `ℝ` | its value at outcome `ω` |

`Fin 2 = {0,1}` indexes the sample, `Fin 13 = {0,…,12}` the observation. So this
is an indexed family of **26 random variables**, each a function `Ω → ℝ`.

This line has no probabilistic content. Nothing here says the `X` are Gaussian,
independent, or even measurable.

### `{P : Measure Ω}`

A measure on `Ω`, using the σ-algebra instance above. Mathlib's `Measure` takes
values in `ℝ≥0∞` and is σ-additive on measurable sets.

Note it is **not** assumed to be a probability measure. That follows from
`h.law`: `P.map (X g i) = gaussianReal μ (variance g)` forces `P univ = 1`.

### `{μ : ℝ}`

The **common mean** — the quantity being estimated. The same `μ` appears for
both samples, which is the entire point of the common-mean problem. Universally
quantified, so dominance is claimed at every real `μ`.

### `{variance : Fin 2 → NNReal}`

The two population variances, as a function from `{0,1}` to the nonnegative
reals: `variance 0 = σ₁²`, `variance 1 = σ₂²`. (Not curried — a single-argument
function, best read as an indexed pair.)

Two points:

* **Indexed by the sample only.** In `h.law` you will see
  `gaussianReal μ (variance g)`, i.e. `variance g` and not `variance g i`. So
  all 13 observations within a sample share one variance, while the two samples
  may differ. That is the intended model.
* **`NNReal` because `gaussianReal` demands it.** Mathlib's definition is
  `gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ`, documented as "a Gaussian
  distribution on `ℝ` with mean `μ` and **variance** `v`". So `v` is the
  variance, not the standard deviation. Note also
  `gaussianReal μ 0 = Measure.dirac μ` — zero variance is permitted by the type
  and yields a degenerate point mass, which is why positivity is assumed
  separately (§3).

All four of these are *implicit* (`{}`), inferred at the call site from `h`.

---

## 3. The hypotheses

### `(h : TwoNormalSamples13 X P μ variance)`

The model assumption, and the only place the probabilistic content lives. Its
definition ([`NormalSample.lean:76`](GraybillDeal/NormalSample.lean)):

```lean
structure TwoNormalSamples13
    (X : Fin 2 → Fin 13 → Ω → ℝ)
    (ℙ : Measure Ω) (μ : ℝ) (variance : Fin 2 → NNReal) : Prop where
  law :
    ∀ g i,
      ProbabilityTheory.HasLaw (X g i)
        (ProbabilityTheory.gaussianReal μ (variance g)) ℙ
  indep :
    ProbabilityTheory.iIndepFun
      (fun gi : Fin 2 × Fin 13 => X gi.1 gi.2) ℙ
```

**This is a definition, not an assertion.** It claims nothing on its own; it
names a property that a four-tuple `(X, ℙ, μ, variance)` may or may not have.
The universal quantification over `X`, `ℙ`, `μ`, `variance` happens one level
up, in the theorem. The `∀ g i` inside `law` quantifies only over the 26 index
pairs.

**`law`.** `HasLaw f ν ℙ` is mathlib's "`f` has distribution `ν`". Its fields
are `aemeasurable` and `map_eq : ℙ.map f = ν` — the pushforward of `ℙ` along `f`
equals `ν`. Pushforward = distribution, so this is the exact law. Quantified
over `g` and `i`: each of the 26 variables is `N(μ, variance g)`.

**`indep`.** `iIndepFun` (the `i` is for *indexed family*) is independence of the
generated σ-algebras. Mathlib's underlying `iIndep` is documented as: for any
finite set of indices and any measurable sets from the respective σ-algebras,
the measure of the intersection equals the product of the measures. That is
**mutual** independence, not pairwise — which is the strength needed here.

The index type is `Fin 2 × Fin 13`, 26 elements, and
`fun gi => X gi.1 gi.2` flattens the curried family. So this asserts joint
independence of **all 26 observations at once**, across samples and within each
sample. (Had it been indexed over `Fin 2` alone, only the two samples would be
independent, with no structure inside them — strictly weaker and insufficient.)

**Net effect:** 26 jointly independent Gaussians, all with mean `μ`, thirteen
with variance `σ₁²` and thirteen with `σ₂²`. This is the standard two-sample
common-mean normal model (see §7).

Note what it deliberately omits: only `AEMeasurable` (inside `HasLaw`), and no
non-degeneracy. Hence the next three hypotheses.

### `(hXmeas : ∀ g i, Measurable (X g i))`

Full measurability of all 26 variables — preimages of Borel sets are
measurable. This is strictly stronger than the `AEMeasurable` carried inside
`h.law`, which only requires agreement almost everywhere with a measurable
function.

Since hypotheses cut against generality, it is worth asking whether the stronger
form is a real restriction. It is not: any `AEMeasurable` function agrees a.e.
with a measurable one and `sqRisk` is an integral, hence invariant under a.e.
modification; the standard definition of "random variable" already includes
measurability; and the witness satisfies it trivially (coordinate projections).

### `(hvariance₀ : 0 < (variance 0 : ℝ))` and `(hvariance₁ : …)`

The variances are strictly positive. The `: ℝ` is the coercion `NNReal → ℝ`;
since `NNReal` is already nonnegative, these are equivalent to `variance g ≠ 0`.

They rule out the degenerate case noted in §2: at zero variance
`gaussianReal μ 0` is a point mass, `S² = 0` almost surely, and the weight
`S₁²/(S₁²+S₂²)` is `0/0`. They cost nothing statistically — the literature
assumes the same.

**These are the only constraints on the parameters**, so the theorem ranges over
the whole space `{(μ, σ₁², σ₂²) : μ ∈ ℝ, σᵢ² > 0}`, with a *strict* inequality
at every point. That is stronger than inadmissibility requires, which would
permit equality at some parameter values.

---

## 4. The conclusion: structure

After the `:` comes the claim, whose shape is

```
sqRisk μ ⟨estimator₁⟩ P   <   sqRisk μ ⟨estimator₂⟩ P
```

`sqRisk` applied to three arguments on each side, with a strict `<` between.
Since `sqRisk` returns a real, the whole conclusion is one inequality between
two real numbers, with no quantifiers of its own.

`fun ω => …` is an anonymous function `Ω → ℝ` — the estimator, as a random
variable. The `let r := …` and `let q := …` are local abbreviations only; they
could be inlined without changing the term.

The two sides are not interchangeable: the left estimator carries the `clip01`
and is the **competitor**; the right is **Graybill–Deal**. So the claim is
"competitor's risk < Graybill–Deal's risk".

### `sqRisk`

[`Risk.lean:21`](GraybillDeal/Risk.lean):

```lean
noncomputable def sqRisk (μ : ℝ) (estimator : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, (estimator ω - μ) ^ 2 ∂P
```

Ordinary squared-error risk: the integral of squared error under `P`. No
normalising constant.

**One caveat worth checking.** Lean's Bochner integral returns `0` for
non-integrable integrands, so in principle an inequality between two `∫`s could
be satisfied by junk values rather than genuine risks. Here both are genuinely
finite, for a reason visible on the face of the statement: both weights lie in
`[0,1]` — `clip01` forces it on the left, and `r = S₁²/(S₁²+S₂²) ∈ [0,1]`
automatically on the right. So both estimators are convex combinations of `X̄₁`
and `X̄₂`, giving `|μ̂ − μ| ≤ |X̄₁ − μ| + |X̄₂ − μ|`, which has finite second
moment under the Gaussian model.

---

## 5. The two estimators

They differ **only** in the weight applied to the mean difference:

```
LHS (competitor):     X̄₁ + clip01( r + ε·r(1−r)(1−2r)(4−q) ) · D
RHS (Graybill–Deal):  X̄₁ + r · D
```

Everything below is built from `X` alone:

| symbol | Lean | definition |
|---|---|---|
| `X̄_g` | `sampleMean13 (X g) ω` | `(∑ i, X i ω) / 13` |
| residual | `sampleResidual13` | `X i ω - sampleMean13 X ω` |
| `RSS_g` | `residualSumSquares13` | `∑ i, sampleResidual13 X ω i ^ 2` |
| `S_g²` | `sampleVariance13` | `residualSumSquares13 X ω / 12` |
| `D` | `meanDifference13 X ω` | `sampleMean13 (X 1) ω - sampleMean13 (X 0) ω` |
| `r` | `let r := …` | `S₁² / (S₁² + S₂²)` |
| `q` | `let q := …` | `13 * D ^ 2 / (S₁² + S₂²)` |
| `ε` | `epsilon13` | `1 / 2000` |
| clipping | `clip01 x` | `min 1 (max 0 x)` |

Note the divisors: `13 = n` for the mean, `12 = n − 1` for the variance (the
usual unbiased estimator).

### The right-hand side is Graybill–Deal, and the orientation self-checks

Graybill–Deal weights each sample mean inversely to its own variance. Multiplying
out the RHS with `D = X̄₂ − X̄₁`:

```
X̄₁ + [S₁²/(S₁²+S₂²)]·(X̄₂ − X̄₁) = (S₂²·X̄₁ + S₁²·X̄₂)/(S₁²+S₂²)
```

The weight on `X̄₁` is `S₂²/(S₁²+S₂²) ∝ 1/S₁²`, and on `X̄₂` is `∝ 1/S₂²`.
Correct. (With equal sample sizes the `n` in the usual `n/Sᵢ²` weights cancels,
which is why it does not appear.)

The orientation is *forced*, so this is self-checking. Flip `D` to `X̄₁ − X̄₂`
while keeping `r = S₁²/(S₁²+S₂²)` and you get `(1+r)X̄₁ − r·X̄₂` — not even a
convex combination, with negative weight on `X̄₂`. So the two consistent
conventions are

* `D = X̄₂ − X̄₁` with `r = S₁²/(S₁²+S₂²)` — what is used here, and
* `D = X̄₁ − X̄₂` with `r = S₂²/(S₁²+S₂²)` — the mirror image,

and any mismatched pairing yields a different estimator. Checking the pair
jointly is therefore stronger than checking each half against a convention.

### The left-hand side is a genuine estimator

Every symbol in it is `r`, `q`, `epsilon13`, or a numeral. Neither `μ` nor
`variance` appears, so it is a function of the data alone — as an estimator must
be. Two details:

* **`epsilon13 : ℝ := 1 / 2000`.** The type ascription is load-bearing. As `ℝ`
  this is real division, ≈ 0.0005. Without the ascription Lean would default the
  numerals to `ℕ`, where `1 / 2000 = 0`, the perturbation would vanish, and the
  competitor would collapse to Graybill–Deal.
* **At `ε = 0` the two estimators coincide** (`clip01 r = r` since
  `r ∈ [0,1]`), so they differ by exactly the perturbation term and nothing
  else.

### Two things about `q` worth understanding

**The factor `13` is load-bearing.** `D` has variance `(σ₁²+σ₂²)/n`, so
`E[nD²] = σ₁² + σ₂²` — exactly the scale of the denominator `S₁²+S₂²`. This
makes `q` **scale-free** (unchanged when both variances are multiplied by a
constant) with expectation about 1, which is what makes comparing it against the
fixed constant `4` in `(4 − q)` meaningful. Drop the `n` and `q` becomes
`O(1/n)`, `(4 − q)` is nearly constant, and the construction degenerates.

**`q` is what escapes the known admissibility result.** Duanmu, Roy and
Schrittesser prove Graybill–Deal is admissible in the class
`C₁ = {X̄₁ + D·φ̂(S₁², S₂²)}`, where the weight depends *only* on the two sample
variances. This competitor's weight depends on `D` as well, through `q`, and so
lies outside `C₁`. That is the one substantive modelling claim in the whole
construction, and it is not something Lean can validate — if the perturbation
used only the `S²`s, this theorem would contradict a published result.

`q` is invariant to the `D`-ordering convention, since `D` is squared.

### A note on reading Lean layout

Indentation is meaningless inside Lean expressions; precedence decides. In

```
sampleMean13 (X 0) ω
  + clip01
      (r + epsilon13 * r * (1 - r) * (1 - 2 * r) * (4 - q))
    * meanDifference13 X ω
```

the layout makes `* meanDifference13` look as though it might attach inside
`clip01`. It does not: function application binds tighter than `*`, which binds
tighter than `+`, so this is `X̄₁ + (clip01(w̃) · D)`. Similarly
`13 * D ^ 2 / (…)` parses as `(13 * D²)/(…)` — and here both groupings give the
same real number anyway.

---

## 6. Non-inlined equivalents

The same estimators are defined without inlining in
[`RawEstimatorCoordinates.lean:43`](GraybillDeal/RawEstimatorCoordinates.lean),
as `rawGraybillDealEstimator13` and `rawClippedPerturbedEstimator13`, built from
`rawGraybillDealWeight13` and `rawQuadraticStatistic13`. These are easier to
read, and the `change` on the first line of the proof asserts the inlined
statement is definitionally the same term — so auditing either version suffices.

---

## 7. Cross-check against the literature and the paper

The model and both estimators match Duanmu–Roy–Schrittesser §5.1
([arXiv:2112.14257](https://arxiv.org/abs/2112.14257)), whose setup reads: "Let
`n > 1` and consider the problem of estimating the common mean `μ` of random
variables `X₁⁽¹⁾,…,X₁⁽ⁿ⁾` and `X₂⁽¹⁾,…,X₂⁽ⁿ⁾`, where for each `i ∈ {1,2}` the
random variables `Xᵢ⁽¹⁾,…,Xᵢ⁽ⁿ⁾` are i.i.d. according to `N(μ, σᵢ)` with unknown
variance `σᵢ²`." They too use equal sample sizes, define
`Sᵢ² = (1/(n−1))∑ⱼ(Xᵢ⁽ʲ⁾ − X̄ᵢ)²`, and write Graybill–Deal as
`X̄₁ + D·φ̂` with `φ̂_GD = S₁²/(S₁²+S₂²)`.

So the independence assumption here is neither stronger nor weaker than the
literature's — it is the same one. (This is the right direction to check:
a *stronger* hypothesis would silently weaken the theorem.)

Against the repository's own paper
([`paper/graybill_deal_reader_edition.pdf`](paper/graybill_deal_reader_edition.pdf)):

| paper | Lean |
|---|---|
| two independent samples, same size `n` | `Fin 2 → Fin 13 → Ω → ℝ`, `iIndepFun` over all 26 |
| `Xᵢⱼ ~ N(μ, σᵢ²)` | `HasLaw (X g i) (gaussianReal μ (variance g))` |
| `μ ∈ ℝ`, `σ₁², σ₂² > 0` unknown | `μ : ℝ`, `hvariance₀`, `hvariance₁` |
| `Sᵢ²` usual unbiased | `residualSumSquares13 / 12` |
| `D = X̄₂ − X̄₁` | `sampleMean13 (X 1) − sampleMean13 (X 0)` |
| `r = S₁²/(S₁²+S₂²)` | `sampleVariance13 (X 0) / (sum)` |
| `q = nD²/(S₁²+S₂²)` | `13 * meanDifference13 ^ 2 / (sum)` |
| `μ̂_GD = X̄₁ + Dr` | RHS estimator |
| `w̃ = r + (1/2000)·r(1−r)(1−2r)(4−q)` | argument of `clip01` |
| `w* = min 1, max 0, w̃` | `clip01 x = min 1 (max 0 x)` |
| `μ̂* = X̄₁ + D·w*` | LHS estimator |

---

## 8. What auditing the statement does and does not establish

**Establishes**, once §1–§7 read correctly and the axiom audit is clean:

* the theorem quantifies over the standard two-sample common-mean normal model,
  with the literature's assumptions and no extra ones;
* the baseline is genuinely the Graybill–Deal estimator;
* the competitor is a genuine estimator, depending only on the data;
* both match the accompanying paper;
* the conclusion is a strict inequality of ordinary squared-error risks, holding
  at every `μ` and every pair of positive variances;
* the proof introduces no `sorry`, no `native_decide`, and no axioms beyond the
  three standard ones.

**Does not establish:**

* **Non-vacuity.** If the four hypotheses were jointly unsatisfiable the theorem
  would be vacuously true. `ModelWitness.lean` addresses this by exhibiting a
  concrete instance (`Ω = (Fin 2 × Fin 13) → ℝ`, `P` a product of 26 Gaussians,
  `X` the coordinate projections) and applying the theorem to it. Only three
  type signatures need reading there; the proofs are mathlib lemmas.
* **Anything beyond `n₁ = n₂ = 13`.** The general equal-size result (`n ≥ 10`)
  is a separate theorem with a much larger dependency closure.
* **Toolchain integrity.** `#print axioms` is only as trustworthy as the kernel
  running it. The repository pins Lean `v4.32.0` and mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`; confirming that revision is
  checked out and locally unmodified is a separate check.
* **The modelling judgement in `q`.** That escaping `C₁` is legitimate is
  mathematics about the problem, not about this proof.

## 9. Commands

```bash
lake build
```

```bash
lake env lean CheckAxioms.lean
```

```bash
lake env lean ModelWitness.lean
```

```bash
git -C .lake/packages/mathlib rev-parse HEAD && git -C .lake/packages/mathlib status --porcelain
```

Every line of the axiom audit should print exactly
`[propext, Classical.choice, Quot.sound]`. `lake build` reporting no work to do
confirms the compiled artifacts correspond to the sources on disk. An empty
`git status` confirms mathlib is unmodified.
