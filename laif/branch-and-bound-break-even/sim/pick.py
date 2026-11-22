"""Pick instances per QOBLIB class: the k smallest by number of variables plus a few spread over sizes."""
import sys, csv, os, glob
Q = sys.argv[1]
classes = {"marketsplit": "01-marketsplit/models/binary_linear/lp_files", "birkhoff": "03-birkhoff/models/integer_linear/lp_files",
           "steiner": "04-steiner/models/integer_linear/lp_files", "independentset": "07-independentset/models/binary_linear/lp_files",
           "network": "08-network/models/integer_lp/lp_files", "topology": "10-topology/models/seidel_linear/lp_files"}
for c, d in classes.items():
    rows = list(csv.DictReader(open(os.path.join(Q, d, "metrics.csv"))))
    rows.sort(key=lambda r: (int(r["num_vars"]), r["file"]))
    n = len(rows); pick = rows[:6] + [rows[int(n * f)] for f in (0.35, 0.5, 0.65) if int(n * f) >= 6]
    for r in pick:
        f = os.path.join(Q, d, r["file"])
        f = f if os.path.exists(f) else f + ".xz"
        if os.path.exists(f):
            print(c, r["num_vars"], r["num_constraints"], f)
