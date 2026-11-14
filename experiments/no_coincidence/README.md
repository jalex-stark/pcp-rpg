# Reversible-circuit no-coincidence experiment

Setup. There are W = 3n wires: x = the first 2n wires and z = the last n. S is the set of inputs with z = 0, and
P(C) says C(S) ∩ S = ∅. A gate is `t ^= f(c1, c2)`, where f is any 2-input Boolean function
(16 truth tables). Every P-check here is exact: C is evaluated, bitsliced, on all 2^(2n) points of S
(`core.c`).

Files:
- `core.c`, `nc.py`: the evaluator, the circuit families, the rewrites, and every verifier component
- `analyze.py`: image "reason degree", the low-degree image tester, knockout analysis
- `mixing.py`, `anneal.py`, `hillclimb.py`, `exp_*.py`, `dissect.py`, `inspect_one.py`: the experiments
- `results/`: raw outputs

Verifier components:

| component | kind | sound for | needs a certificate? |
|---|---|---|---|
| `feistel_test` | 1: tester | average case | no |
| `affine_decide` | 1: tester + exact Gaussian elimination | average case | no |
| `image_test(d)` | 1: tester on S; z-images fit q(z)=1, deg q ≤ d, q(0)=0 | average case | no |
| `segment_check` | 2: type system, Pres;Out;Pres with Pres by per-gate syntax | given its testers | the cut (i,j), but V just searches all O(m²) cuts |
| `affine_ai` | 2: forward abstract interpretation, affine domain + value-numbered fresh variables | **unconditionally (a proof)** | no |
| `cnf_ai` | 2: forward propagation of a 3-CNF invariant, checked locally per gate | **unconditionally (a proof)** | no |

See the chat write-up for the analysis. Its results are in `results/*.txt`.
