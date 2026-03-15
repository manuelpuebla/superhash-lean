/-!
# SuperHash.Security.AlgExpr — Algebraic expression AST for cryptanalytic simplification

## Scope
Models algebraic expressions over natural numbers for verifying cryptanalytic
simplifications. The expression type supports constants, variables, addition,
multiplication, and exponentiation — sufficient to represent S-box degree
polynomials and round function compositions.

## Application
- **AlgExpr**: AST for cryptanalytic expressions
- **eval**: evaluation against variable assignment (environment)
- **degree**: upper bound on algebraic degree (for S-box analysis)
- **size/depth**: cost metrics for simplification verification
- Foundation for ConditionalRewriteRule (sound conditional rewrite rules)

Self-contained: NO dependency on HashOp or CryptoOp. Env := Nat → Nat inline.

## References
- Adapted from TrustHash.AlgExpr (Lean 4.16.0 → Lean 4.28.0)
- OptiSat.NodeOps: expression node operations
- OptiSat.NodeSemantics: semantic evaluation
-/

namespace SuperHash.Security.AlgExpr

-- ============================================================
-- Section 1: Expression AST
-- ============================================================

/-- **Algebraic expression over Nat.**
    Sufficient to represent S-box degree polynomials, round function
    compositions, and power expressions like d^{R_F}.
    (Adapted from OptiSat.NodeOps) -/
inductive AlgExpr where
  | const (n : Nat)
  | var (id : Nat)
  | add (l r : AlgExpr)
  | mul (l r : AlgExpr)
  | pow (base : AlgExpr) (exp : Nat)
  deriving DecidableEq, Repr

/-- **Variable environment: maps variable IDs to Nat values.** -/
abbrev Env := Nat → Nat

-- ============================================================
-- Section 2: Evaluation semantics
-- ============================================================

/-- **Evaluate an algebraic expression against an environment.**
    (Adapted from OptiSat.NodeSemantics.evalOp) -/
def eval : AlgExpr → Env → Nat
  | .const n, _   => n
  | .var id, env  => env id
  | .add l r, env => eval l env + eval r env
  | .mul l r, env => eval l env * eval r env
  | .pow b e, env => (eval b env) ^ e

-- ============================================================
-- Section 3: Degree upper bound
-- ============================================================

/-- **Upper bound on algebraic degree.**
    - const n: degree 0 (constant)
    - var id: degree 1 (linear)
    - add l r: max(deg l, deg r)
    - mul l r: deg l + deg r
    - pow b e: e * deg b
    This is an upper bound (not exact) — sufficient for security analysis. -/
def degree : AlgExpr → Nat
  | .const _   => 0
  | .var _     => 1
  | .add l r   => max (degree l) (degree r)
  | .mul l r   => degree l + degree r
  | .pow b e   => e * degree b

-- ============================================================
-- Section 4: Size and depth metrics
-- ============================================================

/-- **Expression size: total number of nodes.**
    Used as cost metric for simplification (fewer nodes = simpler). -/
def size : AlgExpr → Nat
  | .const _   => 1
  | .var _     => 1
  | .add l r   => 1 + size l + size r
  | .mul l r   => 1 + size l + size r
  | .pow b _   => 1 + size b

/-- **Expression depth: longest path from root to leaf.** -/
def depth : AlgExpr → Nat
  | .const _   => 0
  | .var _     => 0
  | .add l r   => 1 + max (depth l) (depth r)
  | .mul l r   => 1 + max (depth l) (depth r)
  | .pow b _   => 1 + depth b

-- ============================================================
-- Section 5: Evaluation theorems
-- ============================================================

/-- **Constant evaluation.** -/
theorem eval_const (n : Nat) (env : Env) : eval (.const n) env = n := rfl

/-- **Variable evaluation.** -/
theorem eval_var (id : Nat) (env : Env) : eval (.var id) env = env id := rfl

/-- **Addition evaluation.** -/
theorem eval_add (l r : AlgExpr) (env : Env) :
    eval (.add l r) env = eval l env + eval r env := rfl

/-- **Multiplication evaluation.** -/
theorem eval_mul (l r : AlgExpr) (env : Env) :
    eval (.mul l r) env = eval l env * eval r env := rfl

/-- **Power evaluation.** -/
theorem eval_pow (b : AlgExpr) (e : Nat) (env : Env) :
    eval (.pow b e) env = (eval b env) ^ e := rfl

/-- **Addition is commutative under evaluation.**
    (Nat.add_comm) -/
theorem eval_add_comm (l r : AlgExpr) (env : Env) :
    eval (.add l r) env = eval (.add r l) env := by
  simp [eval, Nat.add_comm]

/-- **Multiplication is commutative under evaluation.**
    (Nat.mul_comm) -/
theorem eval_mul_comm (l r : AlgExpr) (env : Env) :
    eval (.mul l r) env = eval (.mul r l) env := by
  simp [eval, Nat.mul_comm]

-- ============================================================
-- Section 6: Degree theorems
-- ============================================================

/-- **Degree of constant is 0.** -/
theorem degree_const (n : Nat) : degree (.const n) = 0 := rfl

/-- **Degree of variable is 1.** -/
theorem degree_var (id : Nat) : degree (.var id) = 1 := rfl

/-- **Degree of addition: max of sub-degrees.** -/
theorem degree_add_le (l r : AlgExpr) :
    degree (.add l r) = max (degree l) (degree r) := rfl

/-- **Degree of multiplication: sum of sub-degrees.** -/
theorem degree_mul_le (l r : AlgExpr) :
    degree (.mul l r) = degree l + degree r := rfl

/-- **Degree of power: exponent times base degree.** -/
theorem degree_pow (b : AlgExpr) (e : Nat) :
    degree (.pow b e) = e * degree b := rfl

-- ============================================================
-- Section 7: Size and depth properties
-- ============================================================

/-- **Size is always positive.** -/
theorem size_pos (e : AlgExpr) : size e ≥ 1 := by
  cases e <;> simp [size] <;> omega

/-- **Depth of const is zero.** -/
theorem depth_leaf_const (n : Nat) : depth (.const n) = 0 := rfl

/-- **Depth of var is zero.** -/
theorem depth_leaf_var (id : Nat) : depth (.var id) = 0 := rfl

/-- **Size of add includes both subtrees.** -/
theorem size_add (l r : AlgExpr) :
    size (.add l r) = 1 + size l + size r := rfl

/-- **Size of mul includes both subtrees.** -/
theorem size_mul (l r : AlgExpr) :
    size (.mul l r) = 1 + size l + size r := rfl

end SuperHash.Security.AlgExpr
