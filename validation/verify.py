#!/usr/bin/env python3
"""Compile and run the Alloy regression checks using the supplied Alloy 6.1 JAR."""
from pathlib import Path
import csv
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
jar = Path(sys.argv[1]).resolve()
work = root / 'validation'
subprocess.run(['javac', '-cp', str(jar), str(work / 'RunAll.java')], check=True)
for model, folder, expected in [
    ('models/ABZ_Table2_corrected.als', 'corrected', ['SAT','SAT','SAT','UNSAT','UNSAT','SAT','SAT']),
    ('diagnostics/ABZ_original_bounded_noise.als', 'original', ['SAT'] * 12),
]:
    subprocess.run(['java', '-cp', str(jar) + ':' + str(work), 'RunAll',
                    str(root / model), str(work / folder), 'true'], check=True)
    with (work / folder / 'results.tsv').open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    actual = [row['result'] for row in rows]
    if actual != expected:
        raise SystemExit(f'{model}: expected {expected}, received {actual}')
print('PASS: corrected Table 2 outcomes, non-vacuity, and original diagnostics')
