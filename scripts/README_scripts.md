# SuperHash v4.0 — LLM-Integrated Design Loop

Python scripts for autonomous cryptographic hash design exploration,
backed by Lean 4 formal verification.

## Architecture

```
design_loop.py       Main orchestrator ("power button")
  |
  +-- rule_proposer.py   Propose rewrite rules (LLM or templates)
  |     |
  |     +-- config.py    LLM endpoints, project paths, prompts
  |
  +-- axle_integration.py  Verify rules via Lean kernel (lake env lean)
  |
  +-- rlvf_reward.py       Multi-level reward: syntax/compile/nonvacuity/Pareto
  |
  +-- proving_pipeline.py  3-layer proof attempt: AXLE/DeepSeek/fine-tuned
  |
  +-- test_discovery.py    Integration tests (all modules)
```

## Quick Start

### 1. Template mode (no LLM required)

Works out of the box with seed rule templates:

```bash
python3 scripts/design_loop.py --model template --rounds 10 --design aes128
```

### 2. Local LLM via Ollama

Install Ollama and pull qwen2.5:

```bash
# macOS
brew install ollama
ollama serve              # start server (runs on localhost:11434)
ollama pull qwen2.5       # download model (~4.5 GB)

# Linux
curl -fsSL https://ollama.com/install.sh | sh
ollama serve
ollama pull qwen2.5
```

Run with local LLM:

```bash
python3 scripts/design_loop.py --model local --rounds 10 --design aes128
```

If Ollama is not running, the script falls back to template mode automatically.

### 3. Claude API via Anthropic

Set your API key:

```bash
export ANTHROPIC_API_KEY="sk-ant-..."
pip install anthropic      # if not installed
```

Run with Claude:

```bash
python3 scripts/design_loop.py --model claude --rounds 5 --design aes128
```

## Available Designs

| Name          | Family  | Description                                        |
|---------------|---------|----------------------------------------------------|
| `aes128`      | SPN     | AES-128: 10 rounds, sbox degree 7, branch 5       |
| `poseidon128` | SPN     | Poseidon: 8 rounds, sbox degree 5, branch 4       |
| `sha256`      | Feistel | SHA-256-like: 64 rounds, round cost 3              |
| `keccak`      | Sponge  | Keccak-like: 24 rounds, 256 capacity, perm cost 5  |
| `chacha`      | ARX     | ChaCha-like: 20 rounds, all costs 1                |

## CLI Reference

### design_loop.py

```
python3 scripts/design_loop.py [OPTIONS]

Options:
  --model MODEL      LLM backend: template, local, claude (default: template)
  --rounds N         Maximum rounds (default: 20)
  --design NAME      Initial design (default: aes128)
  --proposals N      Rules proposed per round (default: 5)
  --seed N           Random seed (default: 42)
  --timeout N        Lean verification timeout in seconds (default: 60)
  --no-verify        Skip Lean compilation (simulate verification)
  --quiet            JSON-only output (no progress)
  --test             Run self-test (fast, no Lean)
  --test --full      Run self-test WITH Lean compilation
  --help             Show help
```

### rule_proposer.py

```
python3 scripts/rule_proposer.py --model local --design aes128 --proposals 5
python3 scripts/rule_proposer.py --island SPN --proposals 10
python3 scripts/rule_proposer.py --test
```

### axle_integration.py

```
python3 scripts/axle_integration.py --candidate rule.json
python3 scripts/axle_integration.py --candidate rule.json --timeout 120
python3 scripts/axle_integration.py --batch rules/
python3 scripts/axle_integration.py --test --full   # with Lean compilation
```

## Example Output

```
============================================================
  SuperHash Design Loop v4.0
============================================================
  Design:   aes128 (AES-128: 10-round SPN, sbox degree 7, linear branch 5)
  Model:    template
  Rounds:   5
  Verify:   no (simulated)
  Converge: stop after 3 rounds without improvement

  Baseline Pareto front:
    Security    Latency      Gates
  ---------- ---------- ----------
         120         10         70

--- Round 1/5 ----------------------------------------
  Proposed: 10 candidates (via template)
  Verified: 10 SOUND
  Pareto:   +0.500 improvement (3 points)
  Time:     0.0s

--- Round 2/5 ----------------------------------------
  Proposed: 10 candidates (via template)
  Verified: 10 SOUND
  Pareto:   no improvement (1/3 toward convergence)
  Time:     0.0s

...

============================================================
  Final Results
============================================================
  Rounds:     5
  Proposed:   50 rules
  Verified:   50 via Lean kernel
  Sound:      50 rules added to pool
  Converged:  yes
  Time:       0.2s

  Final Pareto front:
    Security    Latency      Gates
  ---------- ---------- ----------
         140         12         75
         120         10         70
         115          7         65
```

## Dependencies

- **Python 3.10+** (standard library only for template mode)
- **requests** (for Ollama mode): `pip install requests`
- **anthropic** (for Claude mode): `pip install anthropic`
- **Lean 4 + Lake** (for verification): installed via elan

## Environment Variables

| Variable           | Description                                 | Default                    |
|--------------------|---------------------------------------------|----------------------------|
| `ANTHROPIC_API_KEY`| Anthropic API key for Claude mode           | (none)                     |
| `OLLAMA_URL`       | Ollama server URL                           | `http://localhost:11434`   |
| `SUPERHASH_MODEL`  | Default model if --model not specified      | `template`                 |

## Kill Switch

To stop the loop gracefully mid-execution:

```bash
touch /tmp/superhash_kill
```

The loop finishes the current round and exits. Remove the file before restarting:

```bash
rm /tmp/superhash_kill
```
