### 1. Clone the GitHub Repo
```bash
git clone https://github.com/rngpaper/onlineappendix.git

cd onlineappendix
```

### 2. Initialize Lake
Initialize the Lake project directly in the current directory. This sets up the Lean 4 environment and Mathlib.

Run the following commands in the root of your repository (`onlineappendix` folder):

```bash
# Initialize the project with mathlib
lake init onlineappendix math

# Update dependencies
lake update

# Download pre-built mathlib binaries (saves hours of compiling)
lake exe cache get
```
*   `init`: Sets up Lake in the current directory.
*   `math`: Uses the Mathlib template (required for proofs relying on Mathlib).


### 3. Run the Proofs
You can now check the proofs individually:

**Section 3:**
```bash
lake lean RNG_Lean4_Proof/RNG_Section3_v1.lean
```

**Section 4:**
```bash
lake lean RNG_Lean4_Proof/RNG_Section4_v1.lean
```

**Section 5:**
```bash
lake lean RNG_Lean4_Proof/RNG_Section5_v1.lean
```

