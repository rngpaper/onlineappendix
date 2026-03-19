# Lean 4 Formal Proofs

## File Guide

| File                    | Status                              | Description                                                  |
| ----------------------- | ----------------------------------- | ------------------------------------------------------------ |
| **`RNG_20260220.lean`** | Canonical (zero sorry, zero errors) | All propositions including hump-shaped equilibrium credibility, GMR boundary, conservatism complementarity, welfare results |
| `RNG_Section3_v1.lean`  | Superseded                          | Section 3: GAAP and Non-GAAP Earnings                        |
| `RNG_Section4_v1.lean`  | Superseded                          | Section 4: Market Equilibrium with Debt Financing            |
| `RNG_Section5_v1.lean`  | Superseded                          | Section 5: Policy and Standard Setting                       |

The canonical file `RNG_20260220.lean` contains 30 explicit axioms (14 standard normal properties, 9 mechanical calculus, 6 structural/equilibrium, 1 residual low-noise regime). All other results are derived as theorems.

## How to Run

### 1. Clone the repo

```bash
git clone https://github.com/rngpaper/onlineappendix.git
cd onlineappendix
```

### 2. Initialize Lake

```bash
# Initialize the project with mathlib
lake init onlineappendix math

# Update dependencies
lake update

# Download pre-built mathlib binaries (saves hours of compiling)
lake exe cache get
```

### 3. Check the canonical proof

```bash
lake lean RNG_Lean4_Proof/RNG_20260220.lean
```

A successful run produces no errors and no `sorry` warnings.

### 4. Check the older section files (optional)

```bash
lake lean RNG_Lean4_Proof/RNG_Section3_v1.lean
lake lean RNG_Lean4_Proof/RNG_Section4_v1.lean
lake lean RNG_Lean4_Proof/RNG_Section5_v1.lean
```
