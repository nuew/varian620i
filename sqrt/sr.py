#!/usr/bin/env python
import re
import struct

buf = bytearray(8192)

with open('sr.oct', 'r') as f:
    r = re.compile('^([0-7]+) +([0-7]+) *(.*)?$')
    s = struct.Struct('=H')
    for row in f:
        m = r.match(row)
        off = int(m.group(1), 8) * 2
        val = int(m.group(2), 8)
        print(f"{off:06o} = {val:06o} ({m.group(3)}; {s.pack(val)})")
        s.pack_into(buf, off, val)

with open('sr.bin', 'wb') as f:
    f.write(buf)
