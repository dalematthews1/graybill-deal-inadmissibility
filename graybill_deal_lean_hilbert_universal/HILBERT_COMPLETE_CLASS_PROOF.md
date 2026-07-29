# A Hilbert-space complete-class proof for the universal reduced experiment

## Verdict

The proposed finite-grid/Hilbert-space argument is mathematically viable for
this particular problem and should be preferred to formalizing Brown's full
randomized-procedure theorem.  It uses special features that Brown's general
theorem cannot assume: the parameter and the Bayes actions lie in `[0,1]`,
loss is squared error, the sample space is countably generated, and all
likelihoods are positive probability densities.

The strongest version uses compactness and the finite-intersection property
over **all** parameter values.  It therefore does not require continuity of
the likelihood or risk as a function of `θ`, and it avoids the
dense-parameter/Scheffé step entirely.  The substantive new work is confined
to weak compactness and metrizability of a bounded subset of `L²`, and weak
closedness of its fixed-parameter risk sublevels.

**Machine-checking status.**  The route described below is now fully
implemented and checked.  The final modules are
`UniversalHilbertCompleteClass.lean` and
`UniversalHilbertUnconditionalTheorem.lean`; the final audit is
`UniversalHilbertUnconditionalTheoremAxiomAudit.lean`.  A few
forward-looking implementation notes in the exposition record the design
stage that preceded the completed modules.

## Setup

Fix positive residual degrees of freedom and write

* `Θ = UniversalInteriorTheta = (0,1)`;
* `X = UniversalReducedObservation`;
* `ρ = universalReducedObservationReference
    universalReducedLebesgueMeasure a b`;
* `l_θ(x) = universalReducedLikelihood a b θ x`;
* `P_θ = ρ.withDensity (ENNReal.ofReal ∘ l_θ)`.

The checked theorem
`isProbabilityMeasure_universalReducedLikelihood_withDensity` says that
each `P_θ` is a probability measure, and
`universalReducedLikelihood_pos` says that `l_θ(x)>0` everywhere.  For a
measurable rule `d`, put

\[
  R_\theta(d)=\int_X (d(x)-\theta)^2\,P_\theta(dx)
             =\int_X l_\theta(x)(d(x)-\theta)^2\,\rho(dx).
\]

For `[0,1]`-valued rules this is a finite real number in `[0,1]`; it is the
finite real counterpart of `densitySquaredRisk`.

Assume for contradiction that `d₀` is measurably admissible.  The theorem
`ae_mem_Icc_of_canonicalUniversalReduced_measurablyAdmissible` gives

\[
                 0\leq d_0\leq 1\qquad \rho\text{-a.e.}
\]

Choose a fixed `θ₀∈(0,1)`, for example `θ₀=1/2`, and set `m=P_{θ₀}`.
Positivity of `l_{θ₀}` and `ae_withDensity_iff` imply that `m` and `ρ`
have exactly the same null sets.

Let `H=L²(m)` and

\[
 K=\{d\in H:0\leq d\leq1\quad m\text{-a.e.}\}.
\]

Then `d₀` determines an element of `K`.  The set `K` is convex,
norm-closed, and contained in the unit ball of `H`.  Since `H` is a Hilbert
space, `K` is weakly compact.  It is also weakly metrizable: `X` is a
standard Borel subtype of `ℝ²`, hence its measurable space is countably
generated; `m` is finite; consequently `L²(m)` is separable, and its dual
is separable by the Hilbert-space Riesz equivalence.  Thus the weak topology
on a weakly compact subset of `H` is metrizable.

Both properties must be proved rather than inferred from norm compactness.
A Lean-friendly route is to use `InnerProductSpace.toDual`, transfer
Banach--Alaoglu compactness and `WeakDual.metrizable_of_isCompact` through
the Riesz equivalence, and then pass to the weakly closed subset `K`.

## 1. Weakly closed risk constraints

For every `θ`, `P_θ` is absolutely continuous with respect to `m`: both
have everywhere-positive densities relative to `ρ`.  If `d_n→d` in
`L²(m)`, every subsequence has a further subsequence converging
`m`-almost everywhere and hence `P_θ`-almost everywhere.  Fatou's lemma
therefore gives

\[
                 R_\theta(d)\leq\liminf_n R_\theta(d_n).
\]

Thus `R_θ` is norm-lower-semicontinuous.  It is also convex.  Therefore,
for every extended-real `c`,

\[
             K_{\theta,c}=\{d\in K:R_\theta(d)\leq c\}
\]

is norm-closed and convex, hence weakly closed.  Equivalently, `R_θ|K`
is weakly lower semicontinuous.  Notice that no boundedness of the
likelihood ratio `dP_θ/dm` is required.

**Lean implementation.**  `UniversalHilbertRisk.lean` checks this
`L²` risk-lower-semicontinuity and weak-sublevel-closedness package.  Its
proof uses absolute continuity, an almost-everywhere convergent
subsequence, Fatou's lemma, and equality of norm and weak closures for
convex sets (`Convex.toWeakSpace_closure`).  It does not treat
multiplication by a potentially unbounded likelihood ratio as a bounded
operator.

## 2. A Pareto rule on every finite grid

Let `F⊂Θ` be finite and contain `θ₀`.  Define

\[
 C_F=\{d\in K:R_\theta(d)\leq R_\theta(d_0)
                    \text{ for all }\theta\in F\}.
\]

This set is nonempty because it contains `d₀`; it is weakly closed by the
preceding step and hence weakly compact.  The weakly lower
semicontinuous function

\[
                         S_F(d)=\sum_{\theta\in F}R_\theta(d)
\]

attains its minimum on `C_F`.  Choose a minimizer `d_F`.

It satisfies `R_θ(d_F)≤R_θ(d₀)` on `F`.  It is also Pareto admissible for
the finite grid.  Indeed, if a rule `e` weakly improved `d_F` at every
point of `F` and strictly improved it at one point, first clip `e` to
`[0,1]`.  The clipping theorems in `UniversalCompactAction` show that the
clipped rule remains an improvement and lies in `K`.  Since
`d_F∈C_F`, the clipped rule also belongs to `C_F`, but has strictly
smaller `S_F`, a contradiction.

For the existing separation theorem it is enough to retain the weaker
consequence

\[
       \text{there is no }e\in K\text{ with }
       R_\theta(e)<R_\theta(d_F)\text{ for every }\theta\in F.
\]

These finite-grid rules will supply the finite-intersection property in
Step 4.  Compactness is used twice but for distinct purposes: first to
minimize on each `C_F`, and later to intersect the closed risk constraints
over the entire parameter space.

## 3. The finite-grid rule is a finite-prior Bayes rule

Apply
`FiniteStatisticalRiskSet.exists_positiveFinitePrior_supporting_risk`
with procedure type `K`, risk vector `θ↦R_θ(d)`, and deterministic mixture
`td+(1-t)e`.  Squared-loss convexity supplies its `hmix` hypothesis, and
the preceding Pareto statement supplies `hpareto`.  The result is a
probability prior with finite support (zero supporting weights have
already been deleted) for which `d_F` minimizes finite-prior Bayes risk
over `K`.

Let `b_F` be the corresponding posterior mean.  By
`PositiveFinitePrior.bayesAction_mem_Icc`, `b_F(x)∈[0,1]`, so `b_F∈K`.
The supporting inequality gives

\[
                  \operatorname{BR}(d_F)\leq\operatorname{BR}(b_F).
\]

The posterior Pythagorean theorem
`PositiveFinitePrior.finitePriorBayesRisk_bayes_le` gives the reverse
inequality.  Hence equality holds, and
`PositiveFinitePrior.ae_eq_bayesAction_of_finitePriorBayesRisk_eq`
implies

\[
                         d_F=b_F\qquad \rho\text{-a.e.}
\]

The integrability hypotheses of these theorems are automatic after
normalization because both rules and all target values lie in `[0,1]`;
the posterior total is positive everywhere.

**Lean implementation.**  `UniversalHilbertFiniteGridBayes.lean`,
`UniversalHilbertBayesRiskBridge.lean`,
`UniversalHilbertFiniteGridPosterior.lean`, and
`UniversalHilbertUniversalFiniteGrid.lean` check the supporting-prior,
real/`ENNReal` risk, posterior-identity, and prior-pushforward steps.

Replace each `d_F` by the pointwise posterior-mean representative `b_F`;
this does not change its element of `L²(m)`.

## 4. Compact finite intersections give a global dominator

Define `B₀⊂K` to be the set of `L²(m)` classes represented by positive
finite-prior Bayes rules whose anchor risk is bounded by that of `d₀`:

\[
 B_0=\left\{b_\pi:
   \begin{array}{l}
   \pi\text{ is a positive finite-support prior on }\Theta,\\
   R_{\theta_0}(b_\pi)\leq R_{\theta_0}(d_0)
   \end{array}\right\}.
\]

The definition must retain the existential prior witness.  After choosing
a sequence from `B₀` in Step 6, choice will then supply the corresponding
sequence of `PositiveFinitePrior Θ`.

Let

\[
                         L=\overline{B_0}^{\,w}\subseteq K.
\]

Taking `F={θ₀}` in Steps 2--3 shows that `B₀`, and hence `L`, is nonempty.
The closure is taken in the weak topology on `K` (equivalently in the
ambient weak Hilbert space, since `K` is weakly closed).  The set `L` is
weakly compact because it is weakly closed in the weakly compact set `K`.
For every `θ∈Θ`, put

\[
 A_\theta=\{d\in L:R_\theta(d)\leq R_\theta(d_0)\}.
\]

Step 1 shows that every `A_θ` is weakly closed in `L`.  The family
`(A_θ)_{θ∈Θ}` has the finite-intersection property.  Given a finite
`G⊂Θ`, apply Steps 2--3 to

\[
                              F=G\cup\{\theta_0\}.
\]

The resulting Bayes rule `b_F` satisfies the risk constraints on `F`.
In particular, `R_{θ₀}(b_F)≤R_{θ₀}(d₀)`, so `b_F∈B₀⊂L`, and
`b_F∈A_θ` for every `θ∈G`.  Thus every finite intersection is nonempty.

Compactness of `L` now gives

\[
             d_*\in\bigcap_{\theta\in\Theta}A_\theta,
             \qquad
             R_\theta(d_*)\leq R_\theta(d_0)
             \quad(\theta\in\Theta).
\]

This is the key strengthening over the dense-grid route: no topology on
the parameter space and no continuity in `θ` is used.

## 5. Admissibility identifies the weak limit

Measurable admissibility of `d₀` and the preceding weak domination imply
that no risk inequality is strict; hence

\[
                         R_\theta(d_*)=R_\theta(d_0)
                         \quad\text{for every }\theta.
\]

If `d_*≠d₀` in `L²(m)`, let `\bar d=(d_*+d₀)/2`.  Pointwise completion
of the square gives

\[
 R_\theta(\bar d)
 =\frac{R_\theta(d_*)+R_\theta(d_0)}2
  -\frac14\int_X(d_*-d_0)^2\,dP_\theta
 \leq R_\theta(d_0).
\]

At `θ=θ₀`, `P_{θ₀}=m`, and the final integral is
`\|d_*-d₀\|²_{L²(m)}>0`.  Thus `\bar d` strictly improves at `θ₀`,
contradicting admissibility.  Consequently

\[
                              d_*=d_0\quad\text{in }L^2(m).
\]

This deterministic midpoint argument is why randomized procedures are
unnecessary.  Its integrated midpoint identity and real/`ENNReal`
domination bridge are checked in
`UniversalHilbertStrictMidpoint.lean` and
`UniversalHilbertAdmissibleIdentification.lean`.

Since `d_*∈L` and `d_*=d₀`, this also proves

\[
                              d_0\in\overline{B_0}^{\,w}.
\]

## 6. Extract a Bayes sequence and upgrade it to strong convergence

The weak topology on `K` is metrizable.  Hence membership of `d₀` in the
weak closure of `B₀` supplies a sequence `b_n∈B₀` with

\[
                              b_n\rightharpoonup d_0
                              \quad\text{in }L^2(m).
\]

For each `n`, choose a positive finite-support prior `π_n` witnessing
`b_n∈B₀`; thus `b_n` is represented by the posterior action of `π_n`.
This witness-selection point is necessary: merely choosing an abstract
sequence of `L²` classes would not yet establish
`HasPositiveFiniteBayesApproximation`.

By the definition of `B₀`,

\[
                   R_{\theta_0}(b_n)\leq R_{\theta_0}(d_0)
                   \quad\text{for every }n.
\]

Weak lower semicontinuity and `b_n⇀d₀` give the reverse limiting
inequality, so

\[
                       R_{\theta_0}(b_n)\longrightarrow
                       R_{\theta_0}(d_0).
\]

Since `m=P_{θ₀}`,

\[
                 R_{\theta_0}(d)=\|d-\theta_0\|_{L^2(m)}^2.
\]

Therefore `b_n-\theta₀` converges weakly to `d₀-\theta₀` and its norms
converge.  The Hilbert-space identity

\[
 \|u_n-u\|^2=\|u_n\|^2+\|u\|^2-2\langle u_n,u\rangle
\]

then proves `b_n→d₀` strongly in `L²(m)`.

Strong `L²` convergence yields a further almost-everywhere convergent
subsequence.  The checked implementation uses Mathlib's
`tendstoInMeasure_of_tendsto_Lp` followed by the almost-everywhere
subsequence theorem.  Positivity of `l_{θ₀}` transfers the result from
`m`-a.e. to `ρ`-a.e.  Every term is still the posterior mean of a positive
finite-support prior, so this is exactly
`HasPositiveFiniteBayesApproximation ρ l (fun θ => θ) d₀`.

## Formal-obligation status

| Obligation | Status |
|---|---|
| Likelihood normalization and positivity | Checked |
| Admissible rules are `[0,1]`-valued a.e. | Checked |
| Finite-grid supporting positive prior | Checked |
| Posterior mean lies in `[0,1]` | Checked |
| Bayes-risk Pythagorean identity and a.e. uniqueness | Checked |
| Strong `L²` gap gives an a.e. subsequence | Checked |
| `m=P_{θ₀}` equivalent to `ρ` | Checked |
| Weak compactness and weak metrizability of `K⊂L²(m)` | Checked |
| Weak closedness of bounded-risk constraints | Checked |
| Existence of each finite-grid Pareto minimizer | Checked |
| Map a prior on grid indices to a prior on `Θ` | Checked |
| Finite real-risk/`ENNReal` risk equivalence on `K` | Checked |
| Compact FIP over the closed sets `A_θ` | Checked |
| Sequence extraction from `d₀∈closure B₀`, retaining prior witnesses | Checked |
| Midpoint domination and admissibility identification | Checked |
| Weak plus `θ₀`-risk convergence implies strong `L²` | Checked |
| Complete-class theorem and unconditional raw theorem | Checked |

The aggregate build and the dedicated final audit pass.  The final theorem
depends only on Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`; there are no project-specific axioms or placeholders.
