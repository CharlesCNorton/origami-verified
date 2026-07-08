"""Emit the materialized certificate constants (bezA, bezB, witR36z) from _galois_bezout_cert.json.

The JSON stores the Bezout cofactors A and B as sparse (row, col, value) integer
triples over the bivariate matrices and R36 as its leading-first coefficient
strings; frontier.v materializes the dense constant-first forms.  Default mode
prints the three Coq Definition blocks; --check parses theories/frontier.v and
asserts agreement with the JSON (exact values, padding-insensitive on trailing
zero entries), so the provenance artifact and the source constants stay tied by
generation rather than transcription.  The degree-ten witness campaign reuses
this pipeline with its own certificate file.
"""
import json
import re
import sys

CERT = "_galois_bezout_cert.json"
SRC = "theories/frontier.v"


def load_cert(path=CERT):
    d = json.load(open(path))

    def dense(triples):
        entries = {(int(i), int(j)): int(v) for i, j, v in triples}
        rows = 1 + max(i for i, _ in entries)
        return [
            [entries.get((r, c), 0)
             for c in range(1 + max(j for (i, j) in entries if i == r))]
            for r in range(rows)
        ]

    bez_a = dense(d["A"])
    bez_b = dense(d["B"])
    # the JSON is leading-first; frontier's witR36z is constant-first
    r36 = [int(s) for s in d["R36"]][::-1]
    return bez_a, bez_b, r36


def zlit(n):
    return f"({n})%Z" if n < 0 else f"{n}%Z"


def coq_row(row):
    return "(" + " :: ".join(zlit(v) for v in row) + " :: nil)"


def coq_matrix(name, mat):
    body = "\n  :: ".join(coq_row(r) for r in mat)
    return f"Definition {name} : list (list Z) :=\n  ({body}\n  :: nil).\n"


def coq_list(name, lst):
    return f"Definition {name} : list Z :=\n  {coq_row(lst)}.\n"


def parse_frontier(path=SRC):
    src = open(path).read()

    def coq_def(name, nested):
        if nested:
            m = re.search(
                r"Definition %s : list \(list Z\) :=\n(.*?):: nil\)\." % name,
                src, re.S)
            body = m.group(0).split(":=", 1)[1].rstrip().rstrip(".")
        else:
            m = re.search(r"Definition %s : list Z :=\n(.*?)\.\n" % name,
                          src, re.S)
            body = m.group(1)
        t = (body.replace("%Z", "").replace("::", ",")
                 .replace("nil", "[]").strip())

        def conv(x):
            if isinstance(x, tuple):
                assert x[-1] == []
                return [conv(e) for e in x[:-1]]
            return x

        return conv(eval(t))

    return (coq_def("bezA", True), coq_def("bezB", True),
            coq_def("witR36z", False))


def rows_equal_mod_padding(a, b):
    if len(a) != len(b):
        return False
    for ra, rb in zip(a, b):
        n = max(len(ra), len(rb))
        pa = ra + [0] * (n - len(ra))
        pb = rb + [0] * (n - len(rb))
        if pa != pb:
            return False
    return True


def check():
    ja, jb, jr = load_cert()
    fa, fb, fr = parse_frontier()
    ok_a = rows_equal_mod_padding(ja, fa)
    ok_b = rows_equal_mod_padding(jb, fb)
    ok_r = jr == fr
    print(f"bezA agrees: {ok_a}")
    print(f"bezB agrees: {ok_b}")
    print(f"witR36z agrees (constant-first of the leading-first JSON): {ok_r}")
    if ok_a and ok_b and ok_r:
        print("CERTIFICATE AND SOURCE ARE IN AGREEMENT")
        return 0
    print("MISMATCH BETWEEN CERTIFICATE AND SOURCE")
    return 1


def main():
    if "--check" in sys.argv[1:]:
        sys.exit(check())
    bez_a, bez_b, r36 = load_cert()
    print(coq_matrix("bezA", bez_a))
    print(coq_matrix("bezB", bez_b))
    print(coq_list("witR36z", r36))


if __name__ == "__main__":
    main()
