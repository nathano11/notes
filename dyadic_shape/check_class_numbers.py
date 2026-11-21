"""S3: class numbers h(-4m), h(-8m) by counting reduced forms, for every pair in a scan file.

Usage: python check_class_numbers.py SCAN.csv OUT.csv
Compares with the engine's 2*Phi(0), 2*Phi(-2) and tests prediction S3.
"""
import csv
import sys
import time

import shape_engine as E


def main() -> None:
    rows = list(csv.DictReader(open(sys.argv[1])))
    t0 = time.time()
    bad_s3, bad_engine = [], []
    with open(sys.argv[2], "w") as f:
        f.write("q,d,leg,h4m_forms,h8m_forms,engine_agrees,S3\n")
        for i, r in enumerate(rows):
            q, d, leg = int(r["q"]), int(r["d"]), int(r["leg"])
            m = q * d
            h4, h8 = E.class_number_forms(-4 * m), E.class_number_forms(-8 * m)
            agree = (h4 == int(r["h4m"]) and h8 == int(r["h8m"]))
            if leg == -1:
                ok = h4 % 8 == 4 and h8 % 8 == 4
            else:
                ok = h4 % 8 == 0 and h8 % 8 == 0 and (h4 - h8) % 16 == 0
            if not ok:
                bad_s3.append((q, d, h4, h8))
            if not agree:
                bad_engine.append((q, d, h4, h8, r["h4m"], r["h8m"]))
            f.write(f"{q},{d},{leg},{h4},{h8},{int(agree)},{int(ok)}\n")
            if i % 1000 == 0:
                print(i, len(rows), round(time.time() - t0, 1), flush=True)
    print("pairs", len(rows), "S3 violations", len(bad_s3), bad_s3[:5])
    print("engine/forms disagreements", len(bad_engine), bad_engine[:5])
    print("seconds", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
