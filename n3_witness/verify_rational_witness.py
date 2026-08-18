"""Verify the three-bidder rational certificate using exact arithmetic."""

from fractions import Fraction
import json
from pathlib import Path


WITNESS = Path(__file__).with_name("n3_R2_rational.json")
raw = json.loads(WITNESS.read_text(encoding="utf-8"))
x = [[[Fraction(value) for value in row] for row in plane] for plane in raw]

assert len(x) == 3
assert all(len(plane) == 19 for plane in x)
assert all(len(row) == 19 for plane in x for row in plane)

h = Fraction(1, 12)
one = Fraction(1)
zero = Fraction(0)
failures: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        failures.append(message)


for i1 in range(19):
    for i2 in range(19):
        here = [x[j][i1][i2] for j in range(3)]
        check(sum(here) == one, f"mass@{i1},{i2}")
        check(one >= here[0] >= here[1] >= here[2] >= zero, f"order@{i1},{i2}")
        if i1 == 0:
            check(here[0] == here[1], f"top-tie@{i1},{i2}")
        if i2 == 0:
            check(here[1] == here[2], f"bottom-tie@{i1},{i2}")

        if i1 + 1 < 19:
            there = [x[j][i1 + 1][i2] for j in range(3)]
            check(zero <= there[0] - here[0] <= h, f"own-top@{i1},{i2}")
            check(there[1] <= here[1] and there[2] <= here[2], f"cross-top@{i1},{i2}")

        if i1 >= 1 and i2 + 1 < 19:
            there = [x[j][i1 - 1][i2 + 1] for j in range(3)]
            check(zero <= there[1] - here[1] <= h, f"own-middle@{i1},{i2}")
            check(there[0] <= here[0] and there[2] <= here[2], f"cross-middle@{i1},{i2}")

        if i2 >= 1:
            there = [x[j][i1][i2 - 1] for j in range(3)]
            check(zero <= there[2] - here[2] <= h, f"own-bottom@{i1},{i2}")
            check(there[0] <= here[0] and there[1] <= here[1], f"cross-bottom@{i1},{i2}")

last = 18
for i1 in range(last):
    check(x[2][i1 + 1][last] == x[2][i1][last], f"top-row-x3@{i1}")
    check(x[1][i1][last] - x[1][i1 + 1][last] <= h, f"top-row-x2@{i1}")
for i2 in range(last):
    check(x[0][last][i2 + 1] == x[0][last][i2], f"right-column-x1@{i2}")
    check(x[1][last][i2 + 1] - x[1][last][i2] <= h, f"right-column-x2@{i2}")
for j in range(3):
    for i2 in range(19):
        check(x[j][last][i2] == x[j][last - 1][i2], f"right-band@{j},{i2}")
    for i1 in range(19):
        check(x[j][i1][last] == x[j][i1][last - 1], f"top-band@{j},{i1}")

i1 = int(Fraction(1, 2) / h)
i2 = int(Fraction(3, 4) / h)
allocation = tuple(x[j][i1][i2] for j in range(3))
value = Fraction(5, 4) * allocation[0] + Fraction(3, 4) * allocation[1]
check(all(48 % item.denominator == 0 for plane in x for row in plane for item in row),
      "denominator-not-dividing-48")
check(allocation == (Fraction(11, 12), Fraction(1, 12), zero), "target-allocation")
check(value == Fraction(29, 24), "target-welfare")

if failures:
    raise SystemExit(f"FAIL ({len(failures)}): {failures[:20]}")

print("PASS: exact 19x19 rational certificate")
print(f"target allocation={allocation}, welfare={value}")
