# Condensed Version
> Online Appendix for the Paper "The Role of Non-GAAP Earnings"

This is a condensed and math-focused summary version (this summary is still a work-in-progress) for the paper's modeling.


# 1. Introduction

This study analytically models how a manager's Non-GAAP earnings disclosure $\mathcal{A}$, which is upward biased (proposition 1), depends on intangible asset intensity and borrowing $D_0$ relative to book equity $B_0$ (proposition 2), with the goal being to demonstrate that $\mathcal{A}$ will reduce the cost of debt (proposition 3).

**Desirable results:**

I develop a theoretical framework to explain the economic forces driving the divergence between GAAP and Non-GAAP earnings and demonstrate why this divergence can be efficient. I model a firm whose conservative GAAP earnings serve as a 'hard,' verifiable signal for the contracting needs of creditors but become increasingly uninformative for valuing intangible-intensive firms in the equity market. This creates a demand for a second, valuation-relevant signal: Non-GAAP earnings.

The credibility of this dual signaling is sustained by two mechanisms: a regulatory enforcement threat that acts as a  'gatekeeper' against aggressive reporting, and an endogenous debt premium imposed by creditors who rationally price the default risk associated with reliance on unverifiable information.
The model yields a sorting equilibrium where firms partition into three reporting regimes based on asset intensity and leverage: Silence, Safe Harbor Pooling, and a separating equilibrium of Structural Decoupling. I show that for high-intangibility firms with low-to-moderate leverage, this dual-reporting system is the WACC-minimizing outcome, outperforming both a strict GAAP-Only mandate and a counterfactual fair value regime with only Non-GAAP reporting.
My analysis provides a structural explanation for why dual reporting emerges *endogenously* in modern capital markets and why regulatory attempts to suppress Non-GAAP reporting may be welfare-reducing for high-growth firms.

(Section 2 not included.)

# 3. The Model

### Asset Payoffs

At $t=0$, the firm requires a fixed amount of capital to fund an asset portfolio consisting of tangible assets $K$ in place and intangible asset $I_0$. I assume a capital structure composed of debt with a fixed principal amount of $D_0$ and equity at book value $B_0 = K + I_0 - D_0$.

The manager invests this aggregate capital into the firm's operations, which generate a stochastic terminal liquidating value, $\widetilde{T}_t$, realized at $t=t$. I model this terminal value as the sum of the payoffs from the two distinct asset classes:

$$
\widetilde{T}_t = K + \tilde{I}_t
$$

The intangible payoff is the sum of fundamental productivity $\tilde{\theta}$ (observed by manager) and residual noise $\tilde{\nu}$:

$$
\tilde{I}_t = \tilde{\theta} + \tilde{\nu}
$$

where $\tilde{\theta} \sim N(\mu_\theta, \sigma_\theta^2)$ and $\tilde{\nu} \sim N(0, \sigma_\nu^2)$. 
The total intangible-asset intensity is $\sigma_I^2 = \sigma_\theta^2 + \sigma_\nu^2$.

#### 3.1.1. GAAP Reporting Signal

The mandatory GAAP report $y_G$ is defined as the terminal value perturbed by measurement error $\tilde{\varepsilon}$ and an aggregate conservative bias $(\tilde{g}_R + \tilde{g}_S)$:

$$
y_G = \widetilde{T}_t + \tilde{\varepsilon} - (\tilde{g}_R + \tilde{g}_S)
$$

where the components are defined as follows:

-   **Error term**: $\tilde{\varepsilon} \sim N(0, \sigma_\varepsilon^2)$.
-   **Recurring bias**: $\tilde{g}_R \sim N(\mu_R, \sigma_R^2)$.
-   **Conditional conservatism shock**: $\tilde{g}_S$ follows a mixture distribution:

$$
\tilde{g}_S =
\begin{cases}
    0 & \text{with probability } 1-p \\
    Z & \text{with probability } p, \quad \text{where } Z \sim N(\mu_S, \sigma_S^2).
\end{cases}
$$

The shock parameters are strictly increasing in the firm's intangible intensity, $\sigma_I^2$.

**Assumption 1 (The Intangibility-Shock Link).**
The expected value ($\mu_S$) and variance ($\sigma_S^2$) of the conservatism bias are strictly increasing in the firm's intangible intensity ($\sigma_I^2$). Furthermore, the variance of the conservatism bias is convex in intangible intensity, while the variance of the recurring risk ($\sigma_R^2$) is independent of intangible intensity:

$$
\frac{\partial \mu_S}{\partial \sigma_I^2} > 0, \quad \frac{\partial \sigma_S^2}{\partial \sigma_I^2} > 0, \quad \frac{\partial^2 \sigma_S^2}{\partial (\sigma_I^2)^2} \geq 0, \quad \text{and} \quad \frac{\partial \sigma_R^2}{\partial \sigma_I^2} = 0.
$$

#### 3.1.2. Non-GAAP Signal

The manager chooses a voluntary adjustment $\mathcal{A}$ to produce the Non-GAAP signal $y_{NG}$:

$$
y_{NG} = y_G + \mathcal{A}
$$

**Assumption 2 (Non-negative Adjustments).**

$$
\mathcal{A} \geq 0
$$

#### 3.1.3. Information Structure

The model's frictions stem from the asymmetry between the manager's private information and the market's public signals. All structural parameters are common knowledge, including functional forms for terminal value and reporting, distributional parameters, and agents' objective functions (defined next). At $t=0$, the manager privately observes key shocks, so their information set is:

**Manager**: $\mathcal{I}_M = \{\theta, \tilde{g}_R, \tilde{g}_S\}$.

**External agents** (creditors, investors, regulators) observe only public disclosures:

$$
\Omega = \{y_G, \mathcal{A}\}
$$

Public knowledge: all distributional parameters and functional parameters.

As rational Bayesian updaters, they combine $\Omega$ with prior and belief to form posteriors (e.g. $\widehat\sigma^2_{Creditor}$).

## 2. Agents and Objective Functions

**The Creditor**

Market value of debt $D_0$ (proceeds) is the face value $L(\Omega)$ (amount to be repaid, conditional on information after disclosure $\Omega$) less a default put option $\mathcal{P}_{def}$:

$$
D_0 = L(\Omega) - \mathcal{P}_{def}(E[\widetilde{T}_t|\Omega], L(\Omega), \sigma_{Creditor})
$$

Melton (1974): *On the pricing of corporate debt: The risk structure of interest rates*

The cost of debt (yield) $R_L(\mathcal{A})$ is:

$$
R_L(\Omega) = \frac{L(\Omega) - D_0}{D_0} = \frac{\mathcal{P}_{def}}{D_0}
$$

**The Regulator**

The regulatory cost function depends on the deviation of $\mathcal{A}$ from the recurring bias $\mu_R$ (Safe Harbor) and the truth $\tilde{g}$:

$$
\mathcal{C}_{Reg}(\mathcal{A}, \tilde{g}) =
\begin{cases}
    \gamma \sigma_I^2 +  \psi_I /2 \cdot (\mathcal{A} - \tilde{g})^2 & \text{if } (\mathcal{A} - \mu_R)^2 > \mathcal{M} \\
    0 & \text{otherwise}
\end{cases}
$$

**The Equity Investor**

Equity investors are the firm's residual claimants and are risk-neutral. They price shares based on the value $\widetilde{V}_t$, *net of* cost of regulatory enforcement:

$$
\widetilde{V}_t = \widetilde{T}_t - \mathcal{C}_{Reg}(\Omega, \tilde{g})
$$

The pricing function $P(\Omega | \mathcal{A})$ nets expected costs and a liquidity discount (proportional to conditional variance) from terminal value:

$$
P(\Omega) = E[\widetilde{V}_t \mid \Omega] - D_0(1 + R_L(\Omega)) - \lambda \cdot Var(\widetilde{V}_t \mid \Omega)
$$

**The Manager**

The manager maximizes utility $U_M$, comprising stock price, private benefit $\phi$, and personal falsification cost $\psi_P$:

$$
U_M(\mathcal{A} \mid \mathcal{I}_M) = \phi_1 P(\Omega) + \phi_2(\mathcal{A} - \tilde{g}) - \frac{\psi_P}{2}(\mathcal{A} - \tilde{g})^2
$$
