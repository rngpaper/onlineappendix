# Online Appendix for "The Role of Non-GAAP Earnings"

This repository contains the formal proofs and technical summary for the paper. The mathematical results have been machine-verified using the Lean 4 proof assistant.

## Formal Verification

The proofs compile with **zero `sorry`** (unproved assertions) and **zero errors** using [Lean 4](https://leanprover.github.io/) and [Mathlib4](https://github.com/leanprover-community/mathlib4).

### Canonical file

- [`RNG_20260220.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_20260220.lean) — All propositions, the hump-shaped equilibrium credibility theorem, GMR boundary, conservatism complementarity, and welfare results. 30 explicit axioms remain (14 standard normal properties, 9 mechanical calculus, 6 structural/equilibrium, 1 residual low-noise regime).

### Earlier section-by-section files (superseded)

- [`RNG_Section3_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section3_v1.lean) — Equity-only equilibrium
- [`RNG_Section4_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section4_v1.lean) — Debt financing extension
- [`RNG_Section5_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section5_v1.lean) — Policy and welfare

See [`RNG_Lean4_Proof/README.md`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/README.md) for instructions on running the proofs.

---

## Paper Summary

### Abstract

This study provides a theoretical framework for the economic role of non-GAAP earnings as an equilibrium response to the information gap created by conservative GAAP. Conservative accounting rules deterministically truncate the upside of successful intangible investments, creating a material gap between true economic earnings and reported GAAP earnings. Managers privately observe their firm's intangible productivity and bridge this gap through voluntary non-GAAP disclosure, subject to opportunistic bias disciplined by materiality-scaled enforcement (SEC scrutiny and private litigation).

The model generates a partial pooling equilibrium characterized by a single summary statistic, the Governance-to-Manipulation Ratio (GMR). When the GMR falls below one, manipulation overwhelms the signal, and the market rationally ignores non-GAAP disclosure. This yields an endogenous credibility boundary: firms with sufficiently material economic shocks disclose credibly, while firms with intermediate performance pool into an endogenous cheap talk region. The equilibrium credibility of non-GAAP disclosure is hump-shaped in the materiality of the adjustment.

The analysis establishes that conservative GAAP and informative non-GAAP reporting are complements rather than substitutes. Moving GAAP toward fair value would eliminate the information gap that sustains the disciplining mechanism, causing voluntary disclosure to degenerate into cheap talk (the Fair Value Paradox). Regulations restricting non-GAAP reporting would disproportionately raise the cost of capital for intangible-intensive firms and reduce investment efficiency.

### Model Setup (Section 2)

A single-period economy with a representative firm, manager, and competitive equity market. The firm invests in tangible capital $K$ and intangible capital $I_0$. The intangible return $\tilde{R}_I = \tilde{\theta} + \tilde{v}$ is the sum of a privately observed productivity parameter $\tilde{\theta}$ and idiosyncratic noise $\tilde{v}$. GAAP earnings are a censored version of economic earnings: conservative accounting rules truncate the upside via a recognition threshold, creating an information gap that has the payoff structure of a call option on the intangible return. The manager may voluntarily disclose a non-GAAP adjustment $\mathcal{A}$ to bridge this gap, subject to a quadratic penalty cost scaled with materiality.

### Equilibrium Analysis (Section 3)

**Proposition 1 (GMR Credibility Boundary).** A unique partial pooling equilibrium exists. The manager discloses if and only if the private expectation of the conservative bias exceeds a threshold. Credibility is governed by the Governance-to-Manipulation Ratio (GMR), which aggregates enforcement strength, conservatism, intangible intensity, and hype incentives. When GMR < 1, manipulation dominates and the market ignores non-GAAP disclosure.

**Proposition 2 (Equilibrium Credibility).** The market's pricing weight on non-GAAP disclosure:
- (i) equals zero for non-disclosing firms (pooling region);
- (ii) lies in (0, 1) at the credibility boundary;
- (iii) converges to one as the adjustment becomes extreme;
- (iv) is hump-shaped in the materiality of the information gap, with a unique interior maximum.

Part (iv) is the paper's central characterization result. The proof proceeds by analyzing the manipulation ratio $m(\theta) = 2\theta / [(\psi_0 + \theta^2) \cdot \text{GMR}(\theta)]$ and showing it has a unique maximum via log-concavity arguments and the truncated normal variance bound.

### Real Effects and Complementarity (Section 4)

**Proposition 3 (General Equilibrium).** Investment $I_0^*$ and the credibility boundary $\bar{\theta}^*$ are jointly determined in a fixed-point equilibrium. Higher investment widens the information gap, which strengthens the GMR, which sustains credibility, which lowers the cost of capital, which encourages investment.

**Proposition 4 (Conservatism Complementarity).** More conservative GAAP (higher $\kappa$) strengthens the GMR, lowers the credibility boundary, and increases the probability of credible disclosure. Conservative GAAP and informative non-GAAP reporting are complements, not substitutes.

### Policy Analysis (Section 5)

**Proposition 5 (Welfare).** Banning non-GAAP reporting:
- (i)–(iii) eliminates bias but destroys the information channel;
- (iv) reduces investment efficiency;
- (v) disproportionately harms intangible-intensive firms (welfare loss increasing in $\mu_\theta$).

**The Fair Value Paradox.** Moving GAAP toward fair value ($\kappa \to -\infty$) eliminates the structural censor. Without the information gap, the GMR collapses, and voluntary disclosure degenerates into cheap talk. The total informativeness of the market can decrease when mandatory reporting becomes more informative.

### Empirical Predictions (Section 6)

The model generates cross-sectional predictions:
1. The likelihood of credible non-GAAP disclosure is increasing in the materiality of the information gap and in the strength of governance.
2. Equilibrium credibility is hump-shaped in the materiality of the adjustment.
3. Banning non-GAAP reporting is most value-destroying for firms with high intangible intensity.
4. More conservative GAAP regimes exhibit more prevalent and more credible non-GAAP reporting.
