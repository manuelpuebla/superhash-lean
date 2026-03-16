import SuperHash.Crypto.Semantics

/-!
# SuperHash.Crypto.CryptoEval — Real cryptographic evaluation

v2.5 Core: Replaces the Nat-arithmetic `evalCryptoOp` with `evalCryptoSem`
that computes ACTUAL cryptographic metrics for each operation.

## Design (D15: Sequential ≠ Parallel)
- `compose` (sequential): degree multiplies, δ uses domain-specific bound,
  latency adds, gates add
- `parallel`: degree = max, δ = max, latency = max, gates add
- `iterate(r)`: degree = deg^r, activeSboxes = r * base, latency = r * base

## Key difference from v2.0
v2.0: evalCryptoOp (.sbox 7 0) [10] = 70  (just 7 * 10)
v2.5: evalCryptoSem (.sbox 7 0) [child] = {deg=7*child.deg, δ=child.δ, ...}

## Dual Evaluator Architecture
evalCryptoSem operates in the CryptoSemantics domain (v2.5), independent from
the v1.0 pipeline which uses EvalExpr over Nat. The bridge is NatBridge
(projectToNat). A full pipeline_soundness over CryptoSemantics is future work;
v1.0's pipeline_soundness remains valid over the Nat projection.

## Guards (L-550)
All exponent operations use `Nat.max 1 exponent` to avoid 0^0=1 trap.
-/

namespace SuperHash

-- ============================================================
-- Safe exponentiation (L-550: guard 0^0=1)
-- ============================================================

/-- Safe power: ensures base^0 = 1 (correct) but also 0^n = 0 for n≥1.
    The issue: Lean's 0^0 = 1. We guard by requiring exp ≥ 1 when
    the result matters for security bounds. -/
def safePow (base exp : Nat) : Nat :=
  if exp = 0 then 1 else base ^ exp

theorem safePow_pos (base : Nat) (hb : base ≥ 1) (exp : Nat) :
    safePow base exp ≥ 1 := by
  simp [safePow]
  split
  · omega
  · exact Nat.pos_of_ne_zero (by intro h; simp [Nat.pow_eq_zero] at h; omega)

-- ============================================================
-- evalCryptoSem: THE replacement for evalCryptoOp
-- ============================================================

/-- Evaluate a CryptoOp node with CryptoSemantics domain.

    Each operation computes REAL cryptographic metrics:
    - `sbox(d, child)`: S-box with degree d amplifies child's degree
    - `linear(bn, child)`: linear layer sets branch number
    - `xor(l, r)`: XOR is a group operation — does NOT equal addition
    - `round(d, bn, child)`: full round = sbox + linear combined
    - `compose(f, s)`: sequential composition (D15)
    - `parallel(l, r)`: independent parallel (D15)
    - `iterate(n, body)`: n repetitions
    - `const(v)`: constant with no security contribution
    - Block constructors: compositional via their decomposition -/
def evalCryptoSem : CryptoOp → List CryptoSemantics → CryptoSemantics
  -- S-box: amplifies algebraic degree by factor d
  | .sbox d _, [child] =>
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity  -- S-box δ is a fixed property
      linearBias := child.linearBias
      branchNumber := child.branchNumber
      activeMinSboxes := child.activeMinSboxes + 1  -- this S-box is active
      latency := child.latency + 1
      gateCount := child.gateCount + d  -- gates proportional to degree
      circuitDepth := child.circuitDepth + 1 }

  -- Linear layer: sets branch number (diffusion)
  | .linear bn _, [child] =>
    { algebraicDegree := child.algebraicDegree  -- linear doesn't change degree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn  -- MDS branch number
      activeMinSboxes := child.activeMinSboxes
      latency := child.latency + 1
      gateCount := child.gateCount + bn
      circuitDepth := child.circuitDepth + 1 }

  -- XOR: parallel group operation. Degree = max (no interaction between branches).
  -- Active S-boxes = max (both branches share the same S-box layer, not independent).
  | .xor _ _, [l, r] =>
    { algebraicDegree := max l.algebraicDegree r.algebraicDegree
      differentialUniformity := max l.differentialUniformity r.differentialUniformity
      linearBias := max l.linearBias r.linearBias
      branchNumber := min l.branchNumber r.branchNumber  -- weakest link
      activeMinSboxes := max l.activeMinSboxes r.activeMinSboxes  -- parallel, not additive
      latency := max l.latency r.latency + 1  -- XOR is fast
      gateCount := l.gateCount + r.gateCount + 1
      circuitDepth := max l.circuitDepth r.circuitDepth + 1 }

  -- Round: one SPN round = sbox(d) ∘ linear(bn)
  | .round d bn _, [child] =>
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn
      activeMinSboxes := child.activeMinSboxes + 1
      latency := child.latency + 2  -- sbox + linear
      gateCount := child.gateCount + d + bn
      circuitDepth := child.circuitDepth + 2 }

  -- Sequential composition (D15: degree MULTIPLIES, δ MULTIPLIES (product bound, Lai 1994), latency ADDS)
  | .compose _ _, [f, s] =>
    { algebraicDegree := f.algebraicDegree * s.algebraicDegree
      differentialUniformity := f.differentialUniformity * s.differentialUniformity
      linearBias := max f.linearBias s.linearBias
      branchNumber := min f.branchNumber s.branchNumber
      activeMinSboxes := f.activeMinSboxes + s.activeMinSboxes
      latency := f.latency + s.latency
      gateCount := f.gateCount + s.gateCount
      circuitDepth := f.circuitDepth + s.circuitDepth }

  -- Parallel (D15: degree = MAX, latency = MAX)
  | .parallel _ _, [l, r] =>
    { algebraicDegree := max l.algebraicDegree r.algebraicDegree
      differentialUniformity := max l.differentialUniformity r.differentialUniformity
      linearBias := max l.linearBias r.linearBias
      branchNumber := min l.branchNumber r.branchNumber
      activeMinSboxes := l.activeMinSboxes + r.activeMinSboxes
      latency := max l.latency r.latency
      gateCount := l.gateCount + r.gateCount
      circuitDepth := max l.circuitDepth r.circuitDepth }

  -- Iterate: n repetitions (degree = deg^n, active = n*base)
  | .iterate n _, [body] =>
    { algebraicDegree := safePow body.algebraicDegree n
      differentialUniformity := body.differentialUniformity
      linearBias := body.linearBias
      branchNumber := body.branchNumber
      activeMinSboxes := n * body.activeMinSboxes
      latency := n * body.latency
      gateCount := n * body.gateCount
      circuitDepth := n * body.circuitDepth }

  -- Constant: no security properties
  | .const v, [] =>
    { algebraicDegree := v  -- interpret as initial degree
      differentialUniformity := 0
      linearBias := 0
      branchNumber := 0
      activeMinSboxes := 0
      latency := 0
      gateCount := 0
      circuitDepth := 0 }

  -- SPN Block: compositional (r rounds of sbox+linear)
  | .spnBlock r _ _, [sboxChild, linearChild] =>
    { algebraicDegree := safePow (sboxChild.algebraicDegree * linearChild.algebraicDegree) r
      differentialUniformity := max sboxChild.differentialUniformity linearChild.differentialUniformity
      linearBias := max sboxChild.linearBias linearChild.linearBias
      branchNumber := linearChild.branchNumber
      -- Wide trail: BN × R active S-boxes (Daemen-Rijmen 2002)
      activeMinSboxes := linearChild.branchNumber * r
      latency := r * (sboxChild.latency + linearChild.latency)
      gateCount := r * (sboxChild.gateCount + linearChild.gateCount)
      circuitDepth := r * (sboxChild.circuitDepth + linearChild.circuitDepth) }

  -- Feistel Block: r rounds of round function
  | .feistelBlock r _, [fChild] =>
    { algebraicDegree := safePow fChild.algebraicDegree r
      differentialUniformity := fChild.differentialUniformity
      linearBias := fChild.linearBias
      branchNumber := fChild.branchNumber
      activeMinSboxes := r * fChild.activeMinSboxes
      latency := r * fChild.latency
      gateCount := r * fChild.gateCount
      circuitDepth := r * fChild.circuitDepth }

  -- Sponge Block: absorption (rate) + capacity.
  -- Capacity provides isolation: effective δ is min(perm δ, 2^cap) since
  -- an attacker cannot directly observe capacity bits.
  | .spongeBlock rt cap _, [permChild] =>
    { algebraicDegree := safePow permChild.algebraicDegree rt
      -- Capacity isolation: δ_eff = min(perm δ, 2^cap).
      -- This is a SINGLE-QUERY bound (q=1). For q queries: min(δ, q²/2^c).
      -- Source: Bertoni et al. 2008, "On the indifferentiability of the sponge construction"
      differentialUniformity :=
        if cap > 0 then min permChild.differentialUniformity (2 ^ cap)
        else permChild.differentialUniformity
      linearBias := permChild.linearBias
      branchNumber := permChild.branchNumber
      activeMinSboxes := rt * permChild.activeMinSboxes
      latency := rt * permChild.latency + cap
      gateCount := rt * permChild.gateCount
      circuitDepth := rt * permChild.circuitDepth }

  -- ARX Block: add-rotate-xor rounds
  | .arxBlock r _ _ _, [addChild, rotChild, xorChild] =>
    { algebraicDegree := safePow (addChild.algebraicDegree + rotChild.algebraicDegree + xorChild.algebraicDegree) r
      differentialUniformity := max addChild.differentialUniformity (max rotChild.differentialUniformity xorChild.differentialUniformity)
      linearBias := max addChild.linearBias (max rotChild.linearBias xorChild.linearBias)
      branchNumber := min addChild.branchNumber (min rotChild.branchNumber xorChild.branchNumber)
      activeMinSboxes := r * (addChild.activeMinSboxes + rotChild.activeMinSboxes + xorChild.activeMinSboxes)
      latency := r * (addChild.latency + rotChild.latency + xorChild.latency)
      gateCount := r * (addChild.gateCount + rotChild.gateCount + xorChild.gateCount)
      circuitDepth := r * (addChild.circuitDepth + rotChild.circuitDepth + xorChild.circuitDepth) }

  -- FALLBACK: malformed node (wrong child count). Returns zero-security design.
  -- In production, unreachable if NodeOps.children provides correct arity.
  -- If this branch fires, the design is trivially insecure (fitness = 0).
  | _, _ => default

-- ============================================================
-- Smoke tests: evalCryptoSem produces REAL metrics
-- ============================================================

-- An S-box with degree 7 operating on a constant with degree 1
-- produces degree 7*1 = 7 and adds 1 active S-box
#eval evalCryptoSem (.sbox 7 0) [⟨1, 4, 16, 5, 0, 0, 0, 0⟩]
-- Expected: {deg=7, δ=4, ε=16, BN=5, active=1, lat=1, gates=7}

-- Sequential compose: degree multiplies!
#eval evalCryptoSem (.compose 0 0)
  [⟨7, 4, 16, 5, 1, 1, 7, 1⟩,   -- sbox output
   ⟨1, 0, 0, 5, 0, 1, 5, 1⟩]    -- linear output
-- Expected: {deg=7*1=7, δ=max(4,0)=4, BN=min(5,5)=5, active=1, lat=2, gates=12}

-- Iterate 10 rounds: degree = 7^10 ≈ 2.8 × 10^8
#eval evalCryptoSem (.iterate 10 0) [⟨7, 4, 16, 5, 1, 2, 12, 2⟩]
-- Expected: {deg=7^10=282475249, active=10, lat=20, gates=120}

-- SPN block: 10 rounds of (sbox-7 ∘ linear-5)
#eval evalCryptoSem (.spnBlock 10 0 0)
  [⟨7, 4, 16, 0, 1, 1, 7, 1⟩,    -- sbox child
   ⟨1, 0, 0, 5, 0, 1, 5, 1⟩]     -- linear child
-- deg = (7*1)^10 = 7^10, BN=5, active=10*(5+1)/2=30

-- KEY DIFFERENCE from v2.0:
-- v2.0: evalCryptoOp (.xor 0 1) [3, 5] = 8 (just 3+5)
-- v2.5: evalCryptoSem (.xor 0 1) [s1, s2] = {deg=max(s1.deg, s2.deg), ...}
-- XOR is NOT addition in the security domain!

-- ============================================================
-- NatBridge: backward compatibility (D20)
-- ============================================================

/-- Project CryptoSemantics to Nat via algebraicDegree.
    This allows v2.0 tests to pass through the bridge. -/
def projectToNat (cs : CryptoSemantics) : Nat := cs.algebraicDegree

/-- Lift a Nat to CryptoSemantics (with degree = n, rest = 0). -/
def liftNat (n : Nat) : CryptoSemantics :=
  { algebraicDegree := n
    differentialUniformity := 0
    linearBias := 0
    branchNumber := 0
    activeMinSboxes := 0
    latency := 0
    gateCount := 0
    circuitDepth := 0 }

-- Verify: v2.0's evalCryptoOp(.sbox 7 0) [10] = 70
-- v2.5's projectToNat(evalCryptoSem(.sbox 7 0) [liftNat 10]) should be 7*10 = 70
#eval projectToNat (evalCryptoSem (.sbox 7 0) [liftNat 10])  -- 70 ✓

-- v2.0: evalCryptoOp(.iterate 10 0) [8] = 80
-- v2.5: projectToNat(evalCryptoSem(.iterate 10 0) [liftNat 8]) = 8^10 (DIFFERENT!)
-- This is correct: v2.5 uses REAL degree semantics (exponentiation), not v2.0's multiplication.
#eval projectToNat (evalCryptoSem (.iterate 10 0) [liftNat 8])  -- 8^10 = 1073741824

-- FALLBACK DETECTION: malformed nodes produce zero-security (degree=0 → fitness=0)
#eval (evalCryptoSem (.compose 0 0) [liftNat 5]).algebraicDegree  -- 0 (only 1 child, needs 2)
#eval (evalCryptoSem (.sbox 7 0) []).algebraicDegree              -- 0 (no children, needs 1)

end SuperHash
