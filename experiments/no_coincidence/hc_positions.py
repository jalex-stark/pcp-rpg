import json, numpy as np, sys
R = json.load(open(sys.argv[1])); m = int(sys.argv[2])
acc = np.concatenate([np.array(r["acc"]) for r in R]) / m
print("improving-move positions (deciles of circuit depth):", np.histogram(acc, bins=10, range=(0, 1))[0])
sol = [r for r in R if r["count"] == 0]
print(f"solved {len(sol)}/{len(R)}; iters to solve median {np.median([r['iters'] for r in sol]):.0f}; improving moves median {np.median([len(r['acc']) for r in sol]):.0f}")
