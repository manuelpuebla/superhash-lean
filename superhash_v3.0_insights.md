# Insights: SuperHash v3.0 — Complete CryptoSemantics Rules + Expansion + Diversity

**Fecha**: 2026-03-14
**Base**: v2.9.1 (61 jobs, 0 sorry, 699 thms)

## Hallazgos Clave

### 1. Audit de las 3 reglas pendientes para CryptoSemantics

| Regla | CryptoSemantics Sound? | Razón |
|-------|----------------------|-------|
| **composeAssoc** | ✓ SOUND | Los 7 campos usan operaciones asociativas: mul_assoc (degree), add_assoc (active, latency, gates), max/min assoc (δ, ε, BN) |
| **roundCompose** | ⚠️ UNSOUND | RHS = compose(sbox(d,x), const(b)). `const(b).algebraicDegree = b` pero `const(b).branchNumber = 0`. compose multiplica degrees: `(d*deg) * b ≠ d*deg + b`. La regla descompone round en compose pero la semántica de compose (multiplicativa en degree) difiere de round (aditiva en degree: `d*deg + b`) |
| **iterateCompose** | ✓ SOUND | safePow(safePow(deg,m),n) = safePow(deg,n*m) + los 7 campos usan Nat.mul_assoc |

**Resumen**: 3 de 5 reglas son sound para CryptoSemantics: `iterateOne`, `composeAssoc`, `iterateCompose`. 2 son unsound: `parallelIdentity` (min(bn,0)=0) y `roundCompose` (compose multiplica degrees, round los suma).

### 2. Bridge rules son unidireccionales — necesitamos reversos

Los 4 bridges en BlockBridge.lean van block→primitive. Para exploración bidireccional necesitamos también primitive→block. Esto requiere 4 `RewriteRule` adicionales (swap LHS/RHS).

### 3. pipeline_soundness_crypto — obstáculo es EvalExpr

`optimizeF_soundness` es genuinamente polymorphic. Pero `superhash_pipeline_correct` hardcodea Nat en:
- `PatternSoundRule CryptoOp Nat`
- `env : Nat → Nat`
- `ExtractableSound CryptoOp CryptoExpr Nat`

Falta: `EvalExpr CryptoExpr CryptoSemantics` instance. Pero `CryptoExpr.eval` retorna Nat. Necesitamos `CryptoExpr.evalCS` que retorne CryptoSemantics.

### 4. Plan de expansión: 10 reglas en designLoopStep

```
5 simplificación (Nat):     iterateOne, parallelIdentity, composeAssoc, roundCompose, iterateCompose
3 CS proven:                iterateOne_cs, composeAssoc_cs, iterateCompose_cs
4 bridges forward:          spnBlock→iterate, feistel→iterate, sponge→compose, arx→iterate
4 bridges reverse:          iterate→spnBlock, iterate→feistel, compose→sponge, iterate→arx
1 roundSplit:               iterate(2r, x) → compose(iterate(r,x), iterate(r,x))
```

Con 13+ reglas bidireccionales, la saturación debería producir output.length > 1.
