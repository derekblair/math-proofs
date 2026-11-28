"""Split exact independent-search rows into bounded kernel/replay units."""
from pathlib import Path
import subprocess
import sys
s = subprocess.check_output([sys.executable, "generate_exoo.py", *sys.argv[1:]], text=True)
a = s.index("theorem bound_0")
b = s.index("\ntheorem rows ")
head, lines, tail = s[:a], s[a:b].splitlines(), s[b:]
assert len(lines) == 92
Path("RamseyExooCore.lean").write_text(head + "end Erdos151Ramsey.Exoo\n")
chunks = [(0, 1), (1, 2), (2, 4), (4, 6), (6, 9), (9, 12), (12, 16),
          (16, 24), (24, 32), (32, 46)]
names = []
for i, (u, v) in enumerate(chunks):
    name = f"RamseyExooRows{i}"
    names.append(name)
    Path(name + ".lean").write_text("import RamseyExooCore\n\nnamespace Erdos151Ramsey.Exoo\n"
        "set_option maxHeartbeats 0\nset_option maxRecDepth 4096\n"
        + "\n".join(lines[2*u:2*v]) + "\nend Erdos151Ramsey.Exoo\n")
Path("RamseyExoo.lean").write_text("\n".join("import " + n for n in names)
    + "\n\nnamespace Erdos151Ramsey.Exoo\nset_option maxHeartbeats 0\nset_option maxRecDepth 4096\n" + tail)
Path("exoo-order.txt").write_text("\n".join(["RamseySmall","RamseySearch","RamseyExooCore",*names,"RamseyExoo"]) + "\n")
