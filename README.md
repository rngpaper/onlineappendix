# Online Appendix for the Paper "The Role of Non-GAAP Earnings"

This [Online Appendix](https://github.com/rngpaper/onlineappendix) provides a condensed, math-focused summary of the paper's analytical framework. Section 3 analyzes Non-GAAP disclosure in an equity-only setting. Section 4 introduces debt financing and characterizes the equilibrium with creditor discipline.

## Formal Verification

The mathematical results in this [paper](https://github.com/rngpaper/onlineappendix/blob/main/paper_20260108.pdf) have been formally verified using the [Lean 4](https://leanprover.github.io/) proof assistant. Complete formal proofs are available in the `RNG_Lean4_Proof/` directory:

- **Section 3**: [`RNG_Section3_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section3_v1.lean) — GAAP and Non-GAAP Earnings (Propositions 1-2, Lemmas 3.1-3.2, Corollaries 1 and B.1)
- **Section 4**: [`RNG_Section4_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section4_v1.lean) — Market Equilibrium with Debt Financing (Propositions 3-5, Lemmas 4.1-4.2, Corollaries 3-4)
- **Section 5**: [`RNG_Section5_v1.lean`](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/RNG_Section5_v1.lean) — Policy and Standard Setting (Proposition 6, Lemma A.7, Investment Efficiency, Welfare Analysis)

All theorems, lemmas, and corollaries stated in this document are verified from first principles using Lean 4's type system and mathematical libraries.

An HOWTO guide is available at [https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/README.md](https://github.com/rngpaper/onlineappendix/blob/main/RNG_Lean4_Proof/README.md)

## Technical Summary for the Paper "The Role of Non-GAAP Earnings"

# 1. Introduction

This study analytically models the divergence between GAAP and Non-GAAP earnings not as a failure of standardization, but as a WACC-minimizing architecture that solves a fundamental "impossibility dilemma" in financial reporting.

# **Paper Abstract**

- This study provides a theoretical framework to explain the economic role of non-GAAP earnings as an efficient, equilibrium response to conflicting demands from capital providers. I model a firm serving creditors who require conservative earnings for contracting, and equity investors who require informative signals for valuation.

- In a GAAP-only regime, the model formalizes the fundamental trade-off: raising the recognition threshold toward fair value improves equity informativeness but degrades debt contracting efficiency; maintaining conservatism protects creditors but creates information gaps for equity investors. As a result, any uniform mandatory standard is inherently second-best.

- Conservative accounting creates residual uncertainty that pools firms and increases the cost of equity, creating demand for a second, valuation-relevant signal: non-GAAP earnings. Managers resolve this pooling by voluntarily disclosing a non-GAAP adjustment that reveals unrecognized gains in the GAAP earnings, enabling signal specialization and reducing the cost of equity. However, such disclosure simultaneously increases the cost of debt by exposing asset volatility.

- This trade-off yields a leverage threshold that partitions firms: intangible-intensive firms with low leverage adopt dual reporting to minimize WACC, whereas highly leveraged firms rely on GAAP-only reporting. 

- Policy efforts to force convergence would destroy this efficient sorting mechanism. My analysis provides a structural explanation for why dual reporting emerges endogenously and why regulatory attempts to suppress non-GAAP reporting are most value-destroying for high-growth, intangible-intensive firms.




## 1.1. The Theoretical Framework

**The Two Masters Problem**
The firm faces conflicting demands from two capital providers:
1.  **Stewardship/Contracting (Creditors):** Requires a 'hard,' verifiable lower bound on value to prevent moral hazard. This demands **Conditional Conservatism**.
2.  **Valuation (Equity Investors):** Requires an unbiased, timely estimate of future cash flows, particularly regarding risky growth options (intangibles).

**The Impossibility Dilemma**
A single mandatory signal cannot simultaneously optimize both objectives. A signal conservative enough for debt contracting is structurally too pessimistic for equity valuation. Conversely, a signal capturing intangible growth options is too "soft" for efficient contracting.

**The Solution: The Tinbergen Principle**
Following the Tinbergen Principle (achieving two targets requires two instruments), the economy adopts a **Structural Decoupling**:
*   **Instrument 1 (GAAP):** Specializes in contracting (Maximal Conservatism).
*   **Instrument 2 (Non-GAAP):** Specializes in valuation (Resolution of Uncertainty).

**Investment Efficiency (Real Effects)**
The model extends the Myers-Majluf (1984) framework to disclosure. GAAP-only reporting causes pooling of high-productivity firms, leading to adverse selection and underinvestment. Non-GAAP disclosure restores investment efficiency by allowing separation, though this is constrained by the creditor's pricing of revealed volatility.



# 3. GAAP and Non-GAAP Earnings

## 3.1. Setting up the Model

A single-period economy ($t=0, t$) with a representative firm, manager, and competitive equity market. At $t=0$, the firm invests capital $K$ (tangible) and $I_0$ (intangible). The terminal liquidating value $\widetilde{T}_t$ is realized at $t=t$.

**Assumption 1 (Asset Structure and Payoffs)**

The firm's terminal liquidating value is:

$$
\widetilde{T}_t = K + I_0 + \widetilde{e}_t
\qquad (3.1)
$$

where $\widetilde{e}_t = I_0 \cdot \widetilde{R}_I$ represents the stochastic net earnings. The variable $\widetilde{R}_I$ is the net return on intangible investment:

$$
\tilde{R}_I = \tilde{\theta} + \tilde{v}, \quad \text{where} \quad \tilde{\theta} \sim N(\mu_\theta, \sigma_\theta^2) \quad \text{and} \quad \tilde{v} \sim N(0, \sigma_v^2)
\qquad (3.2)
$$

The manager privately observes $\tilde{\theta}$ at $t=0$. Intangible payoff variance $\sigma_I^2 = I_0^2(\sigma_\theta^2 + \sigma_v^2)$ is strictly increasing in $I_0$.

## 3.2. The Informativeness of GAAP Earnings

**Assumption 2 (GAAP Reporting and Conservative Bias)**

GAAP earnings $y_G$ are a censored version of net economic earnings. Let $\overline{R}_C$ denote the verification threshold for recognizing gains:

$$
y_G = I_0 \min(\widetilde{R}_I, \overline{R}_C) + \tilde{\varepsilon}, \quad \text{where} \quad \tilde{\varepsilon} \sim N(0, \sigma_\varepsilon^2)
\qquad (3.3)
$$

The **Conservative Bias** $\tilde{g}$ is the economic earnings unrecognized by the accounting system:

$$
\tilde{g} \equiv \tilde{e}_t - (y_G - \tilde{\varepsilon}) = I_0 \max(\widetilde{R}_I - \overline{R}_C, 0)
\qquad (3.4)
$$

This has the payoff structure of a call option on the intangible return. The variance of this bias is strictly increasing and strictly convex in intangible intensity $I_0$ (Corollary B.1).

### 3.2.1. Market Valuation with GAAP Only

Consider a benchmark where the only public signal is the mandatory GAAP report ($\Omega = \{y_G\}$).

**Proposition 1 (Market's Non-GAAP Adjustment)**

Under conditional conservatism, the market's rational valuation attempts to reverse the accounting bias. The firm's valuation is:

$$
V(y_G) = E[\tilde{e} \mid y_G] = y_G + \Pr(\tilde{R}_I \ge 0 \mid y_G) \cdot I_0 \mu_+
\qquad (3.5)
$$

where $\mu_+$ is the expected return conditional on a gain.

**Corollary 1 (Residual Uncertainty under GAAP)**

Let $\Sigma_{ND} \equiv \text{Var}(\tilde{e} \mid y_G)$ denote the residual uncertainty. Due to the censoring of gains, uncertainty remains strictly positive and increasing in the firm's expected return:

$$
\Sigma_{ND} = \text{Var}(\tilde{e}) - \text{Var}(E[\tilde{e} \mid y_G]) > 0
\qquad (3.6)
$$

## 3.3. The Non-GAAP Report as a Managerial Response

The manager can voluntarily issue a Non-GAAP metric as a discretionary adjustment applied to the mandatory report:

$$
y_{NG} = y_G + \mathcal{A}
\qquad (3.7)
$$

The manager observes $\mathcal{I}_M = \{\tilde{\theta}, y_G\}$ and forms a private expectation $\hat{g}_M \equiv E[\tilde{g} \mid \mathcal{I}_M]$.

### 3.3.1. Managerial Objectives and Reporting Incentives

**Assumption 3 (Manager's Utility Function)**

The manager chooses $\mathcal{A}$ to maximize utility:

$$
U_M(\mathcal{A} \mid \mathcal{I}_M) = \phi_1 P(\Omega) + \phi_2(\mathcal{A} - \hat{g}_M) - \frac{\psi_P}{2}(\mathcal{A} - \hat{g}_M)^2
\qquad (3.8)
$$

where $\phi_1 \in [0,1]$ (equity stake), $\phi_2 \geq 0$ (hype incentive), and $\psi_P \geq 0$ (penalty cost).

### 3.3.2. Equilibrium Market Pricing

**Assumption 4 (Equity Market Pricing with Liquidity Discount)**

The market prices the firm based on expected terminal value minus a liquidity discount:

$$
P(\Omega) = (K + I_0) + E[\tilde{e} \mid \Omega] - \lambda \cdot \text{Var}(\tilde{e} \mid \Omega)
\qquad (3.9)
$$

**No Disclosure Regime** ($\Omega = \{y_G\}$):

$$
P^{ND} = (K + I_0) + (y_G + E[\tilde{g} \mid y_G]) - \lambda \Sigma_{ND}
\qquad (3.10)
$$

**Disclosure Regime** ($\Omega = \{y_G, \mathcal{A}\}$):

The manager reports $\mathcal{A} = \hat{g}_M + B^*$. Rational investors filter out the equilibrium bias $B^*$:

$$
\hat{g}_M = E[\tilde{g} \mid y_G, \mathcal{A}] = \mathcal{A} - B^*
\qquad (3.11)
$$

The equilibrium price is:

$$
P^{D} = (K + I_{0}) + y_{G} + (\mathcal{A} - B^{*}) - \lambda \Sigma_{D}
\qquad (3.12)
$$

where $\Sigma_{D} \equiv \text{Var}(\tilde{e} \mid y_G, \mathcal{A})$. Disclosure strictly reduces posterior variance ($\Sigma_D < \Sigma_{ND}$). Define the uncertainty reduction ratio:

$$
\omega \equiv \frac{\Sigma_D}{\Sigma_{ND}} \in (0,1)
\qquad (3.13)
$$

**Corollary 2 (Pricing Benefit of Disclosure)**

The valuation wedge between disclosure and no-disclosure regimes is:

$$
P^{D} - P^{ND} = (\hat{g}_{M} - \bar{g}^{ND}) + \Delta_{\text{Liquidity}}
\qquad (3.14)
$$

where $\bar{g}^{ND}$ is the market expectation under silence, and the **Liquidity Benefit** is:

$$
\Delta_{\text{Liquidity}} \equiv \lambda (\Sigma_{ND} - \Sigma_D) = \lambda (1 - \omega) \Sigma_{ND} > 0
\qquad (3.15)
$$

Disclosure increases stock price ($P^D > P^{ND}$) if and only if:

$$
\hat{g}_M > \bar{g}^{ND} - \Delta_{\text{Liquidity}}
\qquad (3.16)
$$

### 3.3.3. Manager's Decision for Non-GAAP Disclosure

**Lemma 3.1 (Optimal Disclosure Threshold)**

The manager discloses Non-GAAP earnings if and only if their private expectation of the conservative bias exceeds a critical threshold:

$$
\text{Disclose} \iff \hat{g}_M \geq g^* = \bar{g}^{ND} + \Delta_{\text{Personal}} - \Delta_{\text{Liquidity}}
\qquad (3.17)
$$

where the opposing wedges are:

$$
\Delta_{\text{Personal}} = \frac{(\phi_1 + \phi_2)(\phi_1 - \phi_2)}{2\phi_1 \psi_P}
\qquad (3.18)
$$

$$
\Delta_{\text{Liquidity}} = \lambda (\Sigma_{ND} - \Sigma_D)
\qquad (3.19)
$$

### 3.3.4. The Optimal Reporting Strategy

The manager chooses $\mathcal{A}$ to maximize:

$$
U_{M}^{D}(\mathcal{A}) = \phi_{1} \left[ (K + I_{0}) + y_{G} + (\mathcal{A} - B^{*}) - \lambda \Sigma_{D} \right] + \phi_{2} (\mathcal{A} - \hat{g}_{M}) - \frac{\psi_{P}}{2} (\mathcal{A} - \hat{g}_{M})^{2}
\qquad (3.20)
$$

**First Order Condition:**

$$
\frac{\partial U_M^D}{\partial \mathcal{A}} = \phi_1 + \phi_2 - \psi_P(\mathcal{A} - \hat{g}_M) = 0
\qquad (3.21)
$$

**Lemma 3.2 (Equilibrium Reporting Bias)**

Conditional on disclosure, the manager systematically overstates the Non-GAAP adjustment. The optimal bias $B^* \equiv \mathcal{A}^* - \hat{g}_M$ is:

$$
B^* = \frac{\phi_1 + \phi_2}{\psi_P}
\qquad (3.22)
$$

### 3.3.5. Equilibrium Characterization

**Proposition 2 (Equilibrium Existence and Uniqueness)**

Under Assumptions 1-4, a unique Bayesian disclosure equilibrium exists:

1. **Disclosure threshold:** The manager discloses if and only if $\hat{g}_M \geq g^*$, where:

$$
g^* = \bar{g}^{ND} + \Delta_{\text{Personal}} - \Delta_{\text{Liquidity}}
\qquad (3.23)
$$

2. **Equilibrium bias:** Conditional on disclosure, $\mathcal{A}^* = \hat{g}_M + B^*$ where:

$$
B^* = \frac{\phi_1 + \phi_2}{\psi_P}
\qquad (3.24)
$$

3. **Market pricing:** Given by Equations (3.10) and (3.12).

**Remark 3.1:** Personal costs $\psi_P > 0$ are necessary for equilibrium existence. As $\psi_P \to 0$, $B^* \to \infty$, rendering the signal uninformative ("cheap talk").

# 4. Market Equilibrium with Debt Financing

Section 3 shows voluntary disclosure is beneficial for shareholders. This section introduces a creditor to examine how leverage acts as a market-based disciplining mechanism on Non-GAAP disclosure.

## 4.1. The Creditor's Pricing Problem

The firm raises required debt financing $D_0$ at $t=0$ from a competitive credit market. The face value $L(\Omega)$ is determined endogenously based on public information $\Omega = \{y_G, \mathcal{A}\}$.

The equity market prices the firm as expected terminal value net of debt repayment, discounted for residual risk:

$$
P(\Omega) = E[\widetilde{T}_t \mid \Omega] - (1 + r_L(\Omega)) D_0 - \lambda \Sigma(\Omega)
\qquad (4.1)
$$

where $r_L(\Omega)$ is the required yield on debt.

### Debt Pricing with Default Risk

Following Merton (1974), the market value of risky debt is the risk-free principal less the value of a 'default put option' $\mathscr{P}_{def}$:

$$
D_0 = L(\Omega) - \mathscr{P}_{def}(\Omega)
\qquad (4.2)
$$

The equilibrium cost of debt is:

$$
r_L(\Omega) = \frac{L(\Omega) - D_0}{D_0} = \frac{\mathscr{P}_{def}(\Omega)}{D_0}
\qquad (4.3)
$$

### Creditor's Volatility Assessment

**Lemma 4.1 (Creditor Volatility Assessment)**

Let $\Sigma_D(\Omega) \equiv \text{Var}(\tilde{e} \mid \Omega)$ denote the creditor's posterior variance. This variance is non-decreasing and convex in the magnitude of the Non-GAAP adjustment:

$$
\frac{\partial \Sigma_D}{\partial \mathcal{A}} \geq 0 \quad \text{and} \quad \frac{\partial^2 \Sigma_D}{\partial \mathcal{A}^2} \geq 0
\qquad (4.4)
$$

**Lemma 4.2 (The Convex Cost of Debt)**

The equilibrium cost of debt $r_L(\mathcal{A})$ is increasing and convex in the magnitude of the Non-GAAP adjustment:

$$
\frac{\partial r_L}{\partial \mathcal{A}} > 0 \quad \text{and} \quad \frac{\partial^2 r_L}{\partial \mathcal{A}^2} > 0
\qquad (4.5)
$$

This convexity creates an endogenous "soft constraint" on reporting, substituting for regulatory penalties.

## 4.2. Equilibrium with Creditor Discipline

### The Manager's Revised Problem

The manager chooses $\mathcal{A}$ to maximize utility, now incorporating the cost of debt service:

$$
\max_{\mathcal{A}} \quad \phi_1 \left[ E[\widetilde{T}_t \mid \Omega] - (1 + r_L(\mathcal{A})) D_0 - \lambda \Sigma_D \right] + \phi_2(\mathcal{A} - \hat{g}_M) - \frac{\psi_P}{2}(\mathcal{A} - \hat{g}_M)^2
\qquad (4.6)
$$

The first-order condition is:

$$ 
\phi_1 (1 - r_L^{\prime}(  \mathcal{A}^{*} ) D_0 ) + 
$$

$$
\phi_2 - \psi_P ( \mathcal{A}^{*} - \hat{g}_M ) = 0
$$

(4.7)


The term $r_L'(\mathcal{A}^*) D_0$ represents the **marginal real cost** of reporting—as the manager inflates the signal, the yield on debt rises, transferring value from equity to debt.

### Equilibrium Characterization

**Proposition 3 (Equilibrium with Creditor Discipline)**

In the presence of risky debt, there exists a unique disclosure equilibrium characterized by:

1. **Disclosure Threshold:** The manager discloses if and only if:

$$
\hat{g}_M \geq g^* = \bar{g}^{ND} + \Delta_{\text{Personal}} - \Delta_{\text{Liquidity}} + \Delta_{\text{Debt}}
\qquad (4.8)
$$

where $\Delta_{\text{Debt}} = (r_L(\mathcal{A}^*) - r_L(0)) D_0 > 0$ represents the real cost of disclosure.

2. **Equilibrium Bias:** Conditional on disclosure, the optimal bias is strictly damped by leverage:

$$
B^* = \frac{\phi_1(1 - r_L'(\mathcal{A}^*) D_0) + \phi_2}{\psi_P}
\qquad (4.9)
$$

3. **Market Pricing:**

$$
P^{ND} = E[\widetilde{T}_t \mid ND] - (1 + r_L(0)) D_0 - \lambda \Sigma_{ND}
\qquad (4.10)
$$

$$
P^{D} = E[\widetilde{T}_t \mid D] - (1 + r_L(\mathcal{A}^*)) D_0 - \lambda \Sigma_{D}
\qquad (4.11)
$$

**Corollary 3 (Creditor Discipline and Loss Reversal)**

The creditor's convex pricing schedule disproportionately disciplines opportunistic loss reversal. Informative Reversal requires adjustment proportional to censored gain. Opportunistic Reversal (hiding a true loss) requires inflated adjustment $\mathcal{A} \gg |y_G|$. Because marginal cost of debt is increasing in $|\mathcal{A}|$, the cost of Opportunistic Reversal is strictly higher.

## 4.3. Real Effects of Non-GAAP Disclosure

**Proposition 4 (Real Effects of Disclosure)**

For a levered firm ($D_0 > 0$), disclosure is not purely informational; it determines the residual terminal value to equity $\widetilde{V}_E$:

$$
\widetilde{V}_E(\Omega) = \widetilde{T}_t - (1 + r_L(\Omega))D_0
\qquad (4.12)
$$

**Decomposition of Price Effect**

The valuation wedge between disclosure and no-disclosure regimes decomposes into three effects:

$$
P^{D} - P^{ND} = \underbrace{(\hat{g}_{M} - \bar{g}^{ND})}_{\text{Information Effect}} + \underbrace{\lambda(\Sigma_{ND} - \Sigma_{D})}_{\text{Liquidity Effect}} - \underbrace{D_{0} \cdot \Delta r_{L}}_{\text{Real Debt Cost}}
\qquad (4.13)
$$

where $\Delta r_L = r_L(\mathcal{A}^*) - r_L(0)$. The **Real Debt Cost** represents a value transfer from shareholders to creditors (Remark 4.2).

## 4.4. WACC Minimization and Leverage Threshold

**Proposition 5 (WACC-Minimizing Disclosure Regime)**

The Dual Reporting regime achieves a lower WACC than the GAAP-only mandate if and only if the firm's initial leverage $D_0$ is below a critical threshold $D^*$:

$$
D_0 < D^* \equiv \frac{\lambda(\Sigma_{ND} - \Sigma_D)}{r_L(\mathcal{A}^*) - r_L(0)}
\qquad (4.16)
$$

The term $D^*$ represents the **informational debt capacity** of the firm. It is the ratio of the total equity benefit of disclosure to the marginal debt cost per dollar of leverage.

### Determinants of the Threshold

**Corollary 4 (Determinants of Informational Debt Capacity)**

The critical leverage threshold $D^*$ is:

1. **Increasing in Illiquidity ($\lambda$):** Higher equity market illiquidity expands the region where disclosure is efficient.
2. **Increasing in GAAP Inefficiency ($\Sigma_{ND} - \Sigma_D$):** High-intangible firms with noisy GAAP earnings have higher informational debt capacity.
3. **Decreasing in Debt Cost Sensitivity ($\Delta r_L$):** When credit markets are highly sensitive to volatility, $D^*$ shrinks.

## 4.5. Agency Conflicts in Disclosure

**Corollary (Agency Cost)**

When the firm is over-leveraged relative to its informational capacity ($D_0 > D^*$) but the manager chooses to disclose (due to private benefits $\phi_2 > 0$), the firm incurs a positive agency cost:

$$
\text{Agency Cost} = \frac{D_0 \cdot \Delta r_L - \lambda(\Sigma_{ND} - \Sigma_D)}{D_0 + P} > 0
\qquad (4.17)
$$

# 5. Discussion: Policy and Standard Setting

## 5.1. The Standard Setter's Dilemma

The regulator sets the recognition threshold $\overline{R}_C$ for mandatory reporting. This creates a fundamental trade-off:
1.  **High $\overline{R}_C$ (Fair Value):** Minimizes $\Sigma_{ND}$ (good for equity valuation) but increases volatility (bad for debt contracting).
2.  **Low $\overline{R}_C$ (Conservatism):** Maximizes contractibility (safe harbor for creditors) but increases information asymmetry (bad for equity).

A single mandatory signal cannot simultaneously optimize $r_L(\overline{R}_C)$ and $r_E(\overline{R}_C)$.

## 5.2. Signal Specialization and Optimal Conservatism

The availability of voluntary Non-GAAP disclosure resolves this dilemma via instrument specialization (Tinbergen Principle).

**Proposition 6 (Optimal Conservatism in Dual-Reporting Regime)**
When voluntary Non-GAAP disclosure is available, the optimal mandatory recognition threshold is a corner solution:

$$
\overline{R}_C^{Dual} = \inf\{\overline{R}_C\} \quad (\text{Maximal Conservatism})
\qquad (5.1)
$$

**Implications:**
1.  **GAAP Specialization:** GAAP specializes entirely in contracting by providing a conservative lower bound (downside protection).
2.  **Non-GAAP Specialization:** Voluntary disclosure specializes in valuation (revealing upside potential).
3.  **Endogenous Sorting:** Firms self-select based on the leverage threshold $D^*$ (Proposition 5). Attempts to force convergence (mandating fair value) or ban Non-GAAP destroy this efficient separation.

## 5.3. Investment Efficiency and Real Effects

Beyond pricing, disclosure affects the real investment level $I_0$.

**The Underinvestment Problem:**
Under GAAP-only reporting, gain-state firms are pooled. The market prices them at the average:

$$
P^{GAAP} = E[\tilde{e} \mid y_G] - \lambda \Sigma_{ND}
\qquad (5.2)
$$

This low valuation creates an adverse selection wedge, causing high-productivity firms ($\text{high } \tilde{\theta}$) to underinvest: $I_0^{GAAP} < I_0^{FB}$.

**Restoring Efficiency:**
Non-GAAP disclosure allows separation ($P^{Dual} > P^{GAAP}$), reducing the cost of capital and stimulating investment.

**Welfare Decomposition:**
The welfare impact of a ban on Non-GAAP disclosure is:

$$
\text{Net Effect} = \underbrace{\text{Elimination of Bias } B^*}_{\text{Benefit}} - \underbrace{\text{Destruction of Separation}}_{\text{Cost}}
\qquad (5.3)
$$

For high-intangible, low-leverage firms, the cost of pooling dominates.

# 6. Empirical Implications

The model generates cross-sectional predictions based on the firm's capital structure and intangible intensity.

## 6.1. Determinants of Disclosure

**Hypothesis 1 (The Leverage-Intangibility Interaction)**
The likelihood of Non-GAAP disclosure is negatively associated with leverage $D_0$ (due to the real debt cost $\Delta r_L$). However, this relationship is attenuated by intangible intensity:

$$
\frac{\partial D^*}{\partial (\Sigma_{ND} - \Sigma_D)} > 0
\qquad (6.1)
$$

High-intangible firms can sustain dual reporting at higher leverage levels because the equity liquidity benefit subsidizes the debt cost.

## 6.2. The Nature of the Signal

**Hypothesis 2 (The Discipline Hypothesis)**
The magnitude of aggressive bias ($NonGAAP > GAAP$) is strictly decreasing in leverage due to creditor discipline. Consequently, income-decreasing ("conservative") Non-GAAP adjustments are concentrated among highly levered firms to lower $r_L$.

## 6.3. Valuation and Cost of Debt

**Hypothesis 3 (Conditional Valuation)**
The Earnings Response Coefficient (ERC) for Non-GAAP news is conditional on leverage:
*   **Low Leverage ($D_0 < D^*$):** Positive ERC (Efficiency Channel).
*   **High Leverage ($D_0 > D^*$):** Lower or negative value impact (Agency Channel/Excessive Disclosure).

**Hypothesis 4 (The Spreads Hypothesis)**
Controlling for fundamental risk, Non-GAAP disclosers exhibit **wider credit spreads** than non-disclosers:

$$
\Delta r_L = r_L(\mathcal{A}^*) - r_L(0) > 0
\qquad (6.2)
$$

Disclosure reveals tail risk (volatility), which rational creditors price into the yield.
